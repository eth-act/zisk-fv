#!/usr/bin/env bash
set -euo pipefail

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
WORKSPACE="$ROOT/build/aeneas-production-extraction"
AENEAS_CHECK_LEAN="${AENEAS_CHECK_LEAN:-1}"
AENEAS_CHECK_FENCE_COMPLETENESS="${AENEAS_CHECK_FENCE_COMPLETENESS:-0}"
AENEAS_CHECK_RV64IM_COMPLETENESS="${AENEAS_CHECK_RV64IM_COMPLETENESS:-0}"
AENEAS_CHECK_RV_COMPLETENESS="${AENEAS_CHECK_RV_COMPLETENESS:-0}"
AENEAS_CHECK_RV_WIDE_SHAPES="${AENEAS_CHECK_RV_WIDE_SHAPES:-0}"

if [[ -z "${AENEAS_FLAKE:-}" ]]; then
  aeneas_owner="$(jq -r '.nodes.aeneas.locked.owner' "$ROOT/flake.lock")"
  aeneas_repo="$(jq -r '.nodes.aeneas.locked.repo' "$ROOT/flake.lock")"
  aeneas_rev="$(jq -r '.nodes.aeneas.locked.rev' "$ROOT/flake.lock")"
  AENEAS_FLAKE="github:$aeneas_owner/$aeneas_repo/$aeneas_rev"
fi

mkdir -p "$WORKSPACE"
rm -rf "$WORKSPACE/Lean"
mkdir -p "$WORKSPACE/lean-check"
rm -f \
  "$WORKSPACE/lean-check/ProductionM2.lean" \
  "$WORKSPACE/lean-check/GeneratedChecks.lean" \
  "$WORKSPACE/lean-check/FenceCompleteness.lean" \
  "$WORKSPACE/lean-check/Rv64imCompleteness.lean" \
  "$WORKSPACE/lean-check/RvCompleteness.lean"
rm -f "$WORKSPACE"/production_m*.llbc

if [[ -f "$AENEAS_FLAKE/backends/lean/Aeneas.lean" ]]; then
  AENEAS_SRC="$AENEAS_FLAKE"
else
  AENEAS_SRC="$(nix flake metadata --json "$AENEAS_FLAKE" | jq -r '.path')"
fi

AENEAS_LEAN_SRC="$AENEAS_SRC/backends/lean"
if [[ ! -f "$AENEAS_LEAN_SRC/Aeneas.lean" ]]; then
  echo "Could not find pinned Aeneas Lean runtime under $AENEAS_LEAN_SRC" >&2
  exit 1
fi

mapfile -t rust_extract_fns < <(
  sed -nE \
    -e 's/^pub fn (extract_[A-Za-z0-9_]+_from_inst)\(.*/\1/p' \
    -e 's/^[a-z0-9_]+_extract!\((extract_[A-Za-z0-9_]+_from_inst),.*/\1/p' \
    "$ROOT/zisk/core/src/aeneas_extract.rs" \
    | sort -u
)

if [[ "${#rust_extract_fns[@]}" -eq 0 ]]; then
  echo "Did not find any Rust extraction wrappers in zisk/core/src/aeneas_extract.rs" >&2
  exit 1
fi

TOOL_SHIMS="$WORKSPACE/tool-shims"
mkdir -p "$TOOL_SHIMS"
for tool in gcc as ar ld; do
  if command -v "riscv64-none-elf-$tool" >/dev/null 2>&1; then
    ln -sf "$(command -v "riscv64-none-elf-$tool")" \
      "$TOOL_SHIMS/riscv64-unknown-elf-$tool"
  fi
done
export PATH="$TOOL_SHIMS:$PATH"

# `zisk-core` embeds this ELF with `include_bytes!`, while Cargo may compile
# zisk-core in parallel with lib-float's build script. Build it up front so the
# extraction harness is not sensitive to Cargo scheduling.
if [[ ! -f "$ROOT/zisk/lib-float/c/lib/ziskfloat.elf" ]]; then
  make -C "$ROOT/zisk/lib-float/c"
fi

mapfile -t raw_extract_fns < <(
  sed -nE \
    -e 's/^pub fn (extract_[A-Za-z0-9_]+_raw(_inst)?)\(.*/\1/p' \
    -e 's/^pub fn (extract_rv64im_opcode_supported)\(.*/\1/p' \
    "$ROOT/zisk/core/src/aeneas_extract.rs" \
    | sort -u
)

starts=()
for fn in "${rust_extract_fns[@]}"; do
  starts+=("crate::aeneas_extract::$fn")
done
for fn in "${raw_extract_fns[@]}"; do
  starts+=("crate::aeneas_extract::$fn")
done

proof_shape_fields=(
  paddr
  op
  aSrc
  aUseSpImm1
  aOffsetImm0
  bSrc
  bUseSpImm1
  bOffsetImm0
  store
  storeOffset
  storePc
  setPc
  indWidth
  jmpOffset1
  jmpOffset2
  isExternalOp
  m32
)

mapfile -t main_extracted_fields < <(
  awk '
    /^structure MainExtractedRow where/ { in_shape = 1; next }
    in_shape && /^namespace ExtractedConst/ { exit }
    in_shape && /^[[:space:]]+[A-Za-z][A-Za-z0-9_]*[[:space:]]*:/ {
      gsub(/^[[:space:]]+/, "")
      split($0, parts, /[[:space:]:]+/)
      print parts[1]
    }
  ' "$ROOT/ZiskFv/Compliance/RowProvenance.lean"
)

if [[ "${proof_shape_fields[*]}" != "${main_extracted_fields[*]}" ]]; then
  echo "Generated proof-row-shape check schema diverges from MainExtractedRow" >&2
  echo "  ProofRowShape fields: ${proof_shape_fields[*]}" >&2
  echo "  MainExtractedRow fields: ${main_extracted_fields[*]}" >&2
  exit 1
fi

charon_starts=()
for start in "${starts[@]}"; do
  charon_starts+=(--start-from "$start")
done

(
  cd "$ROOT/zisk/core"
  nix run "$AENEAS_FLAKE#charon" -- cargo --preset=aeneas \
    "${charon_starts[@]}" \
    --dest-file "$WORKSPACE/production_m2.llbc" \
    -- --lib --features aeneas_extract
)

decl_count="$(jq '.translated.ordered_decls | length' "$WORKSPACE/production_m2.llbc")"
if [[ "$decl_count" -eq 0 ]]; then
  echo "Charon produced an empty production extraction" >&2
  exit 1
fi

(
  cd "$WORKSPACE"
  nix run "$AENEAS_FLAKE#aeneas" -- \
    -backend lean \
    -dest Lean \
    production_m2.llbc
)

generated="$WORKSPACE/Lean/ProductionM2.lean"
if [[ ! -s "$generated" ]]; then
  echo "Aeneas did not produce $generated" >&2
  exit 1
fi

missing_defs=()
for start in "${starts[@]}"; do
  fn="${start##*::}"
  if [[ "$start" == crate::* ]]; then
    if ! grep -q "def aeneas_extract\\.$fn" "$generated"; then
      missing_defs+=("$fn")
    fi
  elif ! grep -q "def .*\\.$fn" "$generated"; then
    missing_defs+=("$fn")
  fi
done

if [[ "${#missing_defs[@]}" -ne 0 ]]; then
  printf 'Generated Lean is missing expected extraction definitions:\n' >&2
  printf '  %s\n' "${missing_defs[@]}" >&2
  exit 1
fi

if grep -En '(^axiom|^opaque|sorry|unknown definitions|HashMap|alloc\.string|alloc\.fmt|Str\.|core\.fmt)' "$generated"; then
  echo "Production extraction generated an unexpected trust marker" >&2
  exit 1
fi

if [[ "$AENEAS_CHECK_LEAN" != 0 ]]; then
  lean_check="$WORKSPACE/lean-check"
  mkdir -p "$lean_check"
  cp "$generated" "$lean_check/ProductionM2.lean"
  if [[ ! -f "$lean_check/aeneas-lean/Aeneas.lean" ]]; then
    rm -rf "$lean_check/aeneas-lean"
    cp -R "$AENEAS_LEAN_SRC" "$lean_check/aeneas-lean"
    chmod -R u+w "$lean_check/aeneas-lean"
  fi

  cat > "$lean_check/lakefile.lean" <<'EOF'
import Lake
open Lake DSL

require aeneas from "aeneas-lean"

package zisk_production_extraction_check

@[default_target] lean_lib ProductionM2
@[default_target] lean_lib GeneratedChecks
lean_lib FenceCompleteness
lean_lib Rv64imCompleteness
lean_lib RvCompleteness
EOF
  rm -f "$lean_check/lean-toolchain"
  cp "$AENEAS_LEAN_SRC/lean-toolchain" "$lean_check/lean-toolchain"

  cat > "$lean_check/GeneratedChecks.lean" <<'EOF'
import ProductionM2

open Aeneas Aeneas.Std Result
open zisk_core

namespace zisk_core_generated_checks

def sampleInst : riscv.riscv_inst.RiscvInstruction :=
  { rom_address := 16#u64
    rvinst := 0#u32
    t := ""
    funct2 := 0#u32
    funct3 := 0#u32
    funct5 := 0#u32
    funct7 := 0#u32
    rd := 3#u32
    rs1 := 5#u32
    rs2 := 7#u32
    rs3 := 0#u32
    imm := 4096#i32
    imme := 0#u32
    inst := ""
    aq := 0#u32
    rl := 0#u32
    csr := 0#u32
    pred := 0#u32
    succ := 0#u32 }

def sampleRs1ZeroInst : riscv.riscv_inst.RiscvInstruction :=
  { sampleInst with rs1 := 0#u32 }

def rowModeProjection
    (result : Result aeneas_extract.ZiskInstExtract) :
    _root_.Option
      (_root_.Nat × _root_.Bool × _root_.Bool × _root_.Bool × _root_.Nat
        × _root_.Nat × _root_.Nat × _root_.Int × _root_.Int) :=
  match result with
  | ok row => some (row.op.val, row.is_external_op, row.m32, row.store_pc,
      row.a_src.val, row.b_src.val, row.store.val, row.jmp_offset1.val, row.jmp_offset2.val)
  | fail _ => none
  | div => none

def rowModeMatches
    (result : Result aeneas_extract.ZiskInstExtract)
    (op : Nat) (isExternal m32 storePc : Bool)
    (aSrc bSrc store : Nat) (jmp1 jmp2 : Int) : Bool :=
  match rowModeProjection result with
  | some actual =>
      actual == (op, isExternal, m32, storePc, aSrc, bSrc, store, jmp1, jmp2)
  | none => false

def rowReturned (result : Result aeneas_extract.ZiskInstExtract) : Bool :=
  match result with
  | ok _ => true
  | fail _ => false
  | div => false

def rawSupported (result : Result Bool) : Bool :=
  match result with
  | ok accepted => accepted
  | fail _ => false
  | div => false

def rawDecodeSupported (result : Result aeneas_extract.Rv64imDecodeExtract) : Bool :=
  match result with
  | ok decoded => decoded.supported
  | fail _ => false
  | div => false

def rawDecodeOpcodeId (result : Result aeneas_extract.Rv64imDecodeExtract) : Nat :=
  match result with
  | ok decoded => decoded.opcode_id.val
  | fail _ => 0
  | div => 0

def rawTranspileAccepted (result : Result aeneas_extract.Rv64imTranspileExtract) : Bool :=
  match result with
  | ok summary => summary.accepted
  | fail _ => false
  | div => false

def rawTranspileAcceptedFlag (result : Result Bool) : Bool :=
  match result with
  | ok accepted => accepted
  | fail _ => false
  | div => false

def rawTranspileMaterializedFlag (result : Result Bool) : Bool :=
  match result with
  | ok materialized => materialized
  | fail _ => false
  | div => false

def resultU32Eq (result : Result Std.U32) (expected : Std.U32) : Bool :=
  match result with
  | ok actual => actual == expected
  | fail _ => false
  | div => false

def rawOpcode (raw : Std.U32) : Result Std.U32 := do
  let masked ← lift (raw &&& 0x7F#u32)
  ok masked

def rawFunct3 (raw : Std.U32) : Result Std.U32 := do
  let masked ← lift (raw &&& 0x7000#u32)
  masked >>> 12#i32

def rawRd (raw : Std.U32) : Result Std.U32 := do
  let masked ← lift (raw &&& 0xF80#u32)
  masked >>> 7#i32

def rawRs1 (raw : Std.U32) : Result Std.U32 := do
  let masked ← lift (raw &&& 0xF8000#u32)
  masked >>> 15#i32

def KnownZiskDecodeGapRaw (raw : Std.U32) : Bool :=
  resultU32Eq (rawOpcode raw) 0x0F#u32 &&
  resultU32Eq (rawFunct3 raw) 0#u32 &&
  !(rawDecodeSupported (aeneas_extract.extract_decode_rv64im_raw raw))

def KnownZiskRowMaterializationGapRaw (raw : Std.U32) : Bool :=
  rawDecodeSupported (aeneas_extract.extract_decode_rv64im_raw raw) &&
  !(rawTranspileMaterializedFlag
      (aeneas_extract.extract_transpile_rv64im_materializes_raw raw))

def KnownZiskGapRaw (raw : Std.U32) : Bool :=
  KnownZiskDecodeGapRaw raw || KnownZiskRowMaterializationGapRaw raw

def rawTranspileRowBSrc (result : Result aeneas_extract.Rv64imTranspileExtract) : Nat :=
  match result with
  | ok summary => summary.row.b_src.val
  | fail _ => 0
  | div => 0

def rawTranspileRowBOffset (result : Result aeneas_extract.Rv64imTranspileExtract) : Nat :=
  match result with
  | ok summary => summary.row.b_offset_imm0.val
  | fail _ => 0
  | div => 0

structure ProofRowShape where
  paddr : _root_.Nat
  op : _root_.Nat
  aSrc : _root_.Nat
  aUseSpImm1 : _root_.Nat
  aOffsetImm0 : _root_.Nat
  bSrc : _root_.Nat
  bUseSpImm1 : _root_.Nat
  bOffsetImm0 : _root_.Nat
  store : _root_.Nat
  storeOffset : _root_.Int
  storePc : _root_.Bool
  setPc : _root_.Bool
  indWidth : _root_.Nat
  jmpOffset1 : _root_.Int
  jmpOffset2 : _root_.Int
  isExternalOp : _root_.Bool
  m32 : _root_.Bool
  deriving BEq

def proofRowShape
    (paddr op aSrc aUseSpImm1 aOffsetImm0 bSrc bUseSpImm1 bOffsetImm0 store : _root_.Nat)
    (storeOffset : _root_.Int)
    (storePc setPc : _root_.Bool)
    (indWidth : _root_.Nat)
    (jmpOffset1 jmpOffset2 : _root_.Int)
    (isExternalOp m32 : _root_.Bool) : ProofRowShape :=
  { paddr, op, aSrc, aUseSpImm1, aOffsetImm0, bSrc, bUseSpImm1, bOffsetImm0,
    store, storeOffset, storePc, setPc, indWidth, jmpOffset1, jmpOffset2,
    isExternalOp, m32 }

def proofRowShapeProjection
    (result : Result aeneas_extract.ZiskInstExtract) :
    _root_.Option ProofRowShape :=
  match result with
  | ok row =>
      some
        { paddr := row.paddr.val
          op := row.op.val
          aSrc := row.a_src.val
          aUseSpImm1 := row.a_use_sp_imm1.val
          aOffsetImm0 := row.a_offset_imm0.val
          bSrc := row.b_src.val
          bUseSpImm1 := row.b_use_sp_imm1.val
          bOffsetImm0 := row.b_offset_imm0.val
          store := row.store.val
          storeOffset := row.store_offset.val
          storePc := row.store_pc
          setPc := row.set_pc
          indWidth := row.ind_width.val
          jmpOffset1 := row.jmp_offset1.val
          jmpOffset2 := row.jmp_offset2.val
          isExternalOp := row.is_external_op
          m32 := row.m32 }
  | fail _ => none
  | div => none

def rowShapeMatches
    (result : Result aeneas_extract.ZiskInstExtract)
    (expected : ProofRowShape) : _root_.Bool :=
  match proofRowShapeProjection result with
  | some actual => actual == expected
  | none => false

def luiRowModeEvidenceMatches
    (result : Result aeneas_extract.ZiskInstExtract) : _root_.Bool :=
  match proofRowShapeProjection result with
  | some row =>
      row.op == 1
      && row.isExternalOp == false
      && row.m32 == false
      && row.setPc == false
      && row.storePc == false
  | none => false

def auipcRowModeEvidenceMatches
    (result : Result aeneas_extract.ZiskInstExtract) : _root_.Bool :=
  match proofRowShapeProjection result with
  | some row =>
      row.op == 0
      && row.isExternalOp == false
      && row.m32 == false
      && row.setPc == false
      && row.storePc == true
  | none => false

def jalRowModeEvidenceMatches
    (result : Result aeneas_extract.ZiskInstExtract) : _root_.Bool :=
  match proofRowShapeProjection result with
  | some row =>
      row.op == 0
      && row.isExternalOp == false
      && row.m32 == false
      && row.setPc == false
      && row.storePc == true
  | none => false

def jalrControlEvidenceMatches
    (result : Result aeneas_extract.ZiskInstExtract) : _root_.Bool :=
  match proofRowShapeProjection result with
  | some row =>
      row.op == 14
      && row.isExternalOp == true
      && row.m32 == false
      && row.setPc == true
      && row.storePc == true
  | none => false

def fencePinsEvidenceMatches
    (result : Result aeneas_extract.ZiskInstExtract) : _root_.Bool :=
  match proofRowShapeProjection result with
  | some row =>
      row.op == 0
      && row.isExternalOp == false
  | none => false

def addViaBinaryShapeEvidenceMatches
    (result : Result aeneas_extract.ZiskInstExtract) : _root_.Bool :=
  match proofRowShapeProjection result with
  | some row =>
      row.op == 10
      && row.isExternalOp == true
      && row.m32 == false
      && row.aSrc == 6
      && row.bSrc == 6
      && row.store == 3
  | none => false

def addiViaBinaryShapeEvidenceMatches
    (result : Result aeneas_extract.ZiskInstExtract) : _root_.Bool :=
  match proofRowShapeProjection result with
  | some row =>
      row.op == 10
      && row.isExternalOp == true
      && row.m32 == false
      && row.aSrc == 6
      && row.bSrc == 2
      && row.store == 3
  | none => false

def addwShapeEvidenceMatches
    (result : Result aeneas_extract.ZiskInstExtract) : _root_.Bool :=
  match proofRowShapeProjection result with
  | some row =>
      row.op == 26
      && row.isExternalOp == true
      && row.m32 == true
      && row.aSrc == 6
      && row.bSrc == 6
      && row.store == 3
  | none => false

def subShapeEvidenceMatches
    (result : Result aeneas_extract.ZiskInstExtract) : _root_.Bool :=
  match proofRowShapeProjection result with
  | some row =>
      row.op == 11
      && row.isExternalOp == true
      && row.m32 == false
      && row.aSrc == 6
      && row.bSrc == 6
      && row.store == 3
  | none => false

def subwShapeEvidenceMatches
    (result : Result aeneas_extract.ZiskInstExtract) : _root_.Bool :=
  match proofRowShapeProjection result with
  | some row =>
      row.op == 27
      && row.isExternalOp == true
      && row.m32 == true
      && row.aSrc == 6
      && row.bSrc == 6
      && row.store == 3
  | none => false

def addiwShapeEvidenceMatches
    (result : Result aeneas_extract.ZiskInstExtract) : _root_.Bool :=
  match proofRowShapeProjection result with
  | some row =>
      row.op == 26
      && row.isExternalOp == true
      && row.m32 == true
      && row.aSrc == 6
      && row.bSrc == 2
      && row.store == 3
  | none => false

def andShapeEvidenceMatches
    (result : Result aeneas_extract.ZiskInstExtract) : _root_.Bool :=
  match proofRowShapeProjection result with
  | some row =>
      row.op == 14
      && row.isExternalOp == true
      && row.m32 == false
      && row.aSrc == 6
      && row.bSrc == 6
      && row.store == 3
  | none => false

def orShapeEvidenceMatches
    (result : Result aeneas_extract.ZiskInstExtract) : _root_.Bool :=
  match proofRowShapeProjection result with
  | some row =>
      row.op == 15
      && row.isExternalOp == true
      && row.m32 == false
      && row.aSrc == 6
      && row.bSrc == 6
      && row.store == 3
  | none => false

def xorShapeEvidenceMatches
    (result : Result aeneas_extract.ZiskInstExtract) : _root_.Bool :=
  match proofRowShapeProjection result with
  | some row =>
      row.op == 16
      && row.isExternalOp == true
      && row.m32 == false
      && row.aSrc == 6
      && row.bSrc == 6
      && row.store == 3
  | none => false

def sltShapeEvidenceMatches
    (result : Result aeneas_extract.ZiskInstExtract) : _root_.Bool :=
  match proofRowShapeProjection result with
  | some row =>
      row.op == 7
      && row.isExternalOp == true
      && row.m32 == false
      && row.aSrc == 6
      && row.bSrc == 6
      && row.store == 3
  | none => false

def sltuShapeEvidenceMatches
    (result : Result aeneas_extract.ZiskInstExtract) : _root_.Bool :=
  match proofRowShapeProjection result with
  | some row =>
      row.op == 6
      && row.isExternalOp == true
      && row.m32 == false
      && row.aSrc == 6
      && row.bSrc == 6
      && row.store == 3
  | none => false

def andiShapeEvidenceMatches
    (result : Result aeneas_extract.ZiskInstExtract) : _root_.Bool :=
  match proofRowShapeProjection result with
  | some row =>
      row.op == 14
      && row.isExternalOp == true
      && row.m32 == false
      && row.aSrc == 6
      && row.bSrc == 2
      && row.store == 3
  | none => false

def oriShapeEvidenceMatches
    (result : Result aeneas_extract.ZiskInstExtract) : _root_.Bool :=
  match proofRowShapeProjection result with
  | some row =>
      row.op == 15
      && row.isExternalOp == true
      && row.m32 == false
      && row.aSrc == 6
      && row.bSrc == 2
      && row.store == 3
  | none => false

def xoriShapeEvidenceMatches
    (result : Result aeneas_extract.ZiskInstExtract) : _root_.Bool :=
  match proofRowShapeProjection result with
  | some row =>
      row.op == 16
      && row.isExternalOp == true
      && row.m32 == false
      && row.aSrc == 6
      && row.bSrc == 2
      && row.store == 3
  | none => false

def sltiShapeEvidenceMatches
    (result : Result aeneas_extract.ZiskInstExtract) : _root_.Bool :=
  match proofRowShapeProjection result with
  | some row =>
      row.op == 7
      && row.isExternalOp == true
      && row.m32 == false
      && row.aSrc == 6
      && row.bSrc == 2
      && row.store == 3
  | none => false

def sltiuShapeEvidenceMatches
    (result : Result aeneas_extract.ZiskInstExtract) : _root_.Bool :=
  match proofRowShapeProjection result with
  | some row =>
      row.op == 6
      && row.isExternalOp == true
      && row.m32 == false
      && row.aSrc == 6
      && row.bSrc == 2
      && row.store == 3
  | none => false

def sllShapeEvidenceMatches
    (result : Result aeneas_extract.ZiskInstExtract) : _root_.Bool :=
  match proofRowShapeProjection result with
  | some row =>
      row.op == 33
      && row.isExternalOp == true
      && row.m32 == false
      && row.aSrc == 6
      && row.bSrc == 6
      && row.store == 3
  | none => false

def srlShapeEvidenceMatches
    (result : Result aeneas_extract.ZiskInstExtract) : _root_.Bool :=
  match proofRowShapeProjection result with
  | some row =>
      row.op == 34
      && row.isExternalOp == true
      && row.m32 == false
      && row.aSrc == 6
      && row.bSrc == 6
      && row.store == 3
  | none => false

def sraShapeEvidenceMatches
    (result : Result aeneas_extract.ZiskInstExtract) : _root_.Bool :=
  match proofRowShapeProjection result with
  | some row =>
      row.op == 35
      && row.isExternalOp == true
      && row.m32 == false
      && row.aSrc == 6
      && row.bSrc == 6
      && row.store == 3
  | none => false

def slliShapeEvidenceMatches
    (result : Result aeneas_extract.ZiskInstExtract) : _root_.Bool :=
  match proofRowShapeProjection result with
  | some row =>
      row.op == 33
      && row.isExternalOp == true
      && row.m32 == false
      && row.aSrc == 6
      && row.bSrc == 2
      && row.store == 3
  | none => false

def srliShapeEvidenceMatches
    (result : Result aeneas_extract.ZiskInstExtract) : _root_.Bool :=
  match proofRowShapeProjection result with
  | some row =>
      row.op == 34
      && row.isExternalOp == true
      && row.m32 == false
      && row.aSrc == 6
      && row.bSrc == 2
      && row.store == 3
  | none => false

def sraiShapeEvidenceMatches
    (result : Result aeneas_extract.ZiskInstExtract) : _root_.Bool :=
  match proofRowShapeProjection result with
  | some row =>
      row.op == 35
      && row.isExternalOp == true
      && row.m32 == false
      && row.aSrc == 6
      && row.bSrc == 2
      && row.store == 3
  | none => false

def sllwShapeEvidenceMatches
    (result : Result aeneas_extract.ZiskInstExtract) : _root_.Bool :=
  match proofRowShapeProjection result with
  | some row =>
      row.op == 36
      && row.isExternalOp == true
      && row.m32 == true
      && row.aSrc == 6
      && row.bSrc == 6
      && row.store == 3
  | none => false

def srlwShapeEvidenceMatches
    (result : Result aeneas_extract.ZiskInstExtract) : _root_.Bool :=
  match proofRowShapeProjection result with
  | some row =>
      row.op == 37
      && row.isExternalOp == true
      && row.m32 == true
      && row.aSrc == 6
      && row.bSrc == 6
      && row.store == 3
  | none => false

def srawShapeEvidenceMatches
    (result : Result aeneas_extract.ZiskInstExtract) : _root_.Bool :=
  match proofRowShapeProjection result with
  | some row =>
      row.op == 38
      && row.isExternalOp == true
      && row.m32 == true
      && row.aSrc == 6
      && row.bSrc == 6
      && row.store == 3
  | none => false

def slliwShapeEvidenceMatches
    (result : Result aeneas_extract.ZiskInstExtract) : _root_.Bool :=
  match proofRowShapeProjection result with
  | some row =>
      row.op == 36
      && row.isExternalOp == true
      && row.m32 == true
      && row.aSrc == 6
      && row.bSrc == 2
      && row.store == 3
  | none => false

def srliwShapeEvidenceMatches
    (result : Result aeneas_extract.ZiskInstExtract) : _root_.Bool :=
  match proofRowShapeProjection result with
  | some row =>
      row.op == 37
      && row.isExternalOp == true
      && row.m32 == true
      && row.aSrc == 6
      && row.bSrc == 2
      && row.store == 3
  | none => false

def sraiwShapeEvidenceMatches
    (result : Result aeneas_extract.ZiskInstExtract) : _root_.Bool :=
  match proofRowShapeProjection result with
  | some row =>
      row.op == 38
      && row.isExternalOp == true
      && row.m32 == true
      && row.aSrc == 6
      && row.bSrc == 2
      && row.store == 3
  | none => false

def storeShapeEvidenceMatches
    (result : Result aeneas_extract.ZiskInstExtract)
    (width : _root_.Nat) : _root_.Bool :=
  match proofRowShapeProjection result with
  | some row =>
      row.op == 1
      && row.isExternalOp == false
      && row.m32 == false
      && row.aSrc == 6
      && row.aUseSpImm1 == 0
      && row.aOffsetImm0 == 5
      && row.bSrc == 6
      && row.bUseSpImm1 == 0
      && row.bOffsetImm0 == 7
      && row.store == 2
      && row.storeOffset == 4096
      && row.storePc == false
      && row.setPc == false
      && row.indWidth == width
      && row.jmpOffset1 == 4
      && row.jmpOffset2 == 4
  | none => false

def loadShapeEvidenceMatches
    (result : Result aeneas_extract.ZiskInstExtract)
    (width : _root_.Nat) : _root_.Bool :=
  match proofRowShapeProjection result with
  | some row =>
      row.op == 1
      && row.isExternalOp == false
      && row.m32 == false
      && row.aSrc == 6
      && row.aUseSpImm1 == 0
      && row.aOffsetImm0 == 5
      && row.bSrc == 5
      && row.bUseSpImm1 == 0
      && row.bOffsetImm0 == 4096
      && row.store == 3
      && row.storeOffset == 3
      && row.storePc == false
      && row.setPc == false
      && row.indWidth == width
      && row.jmpOffset1 == 4
      && row.jmpOffset2 == 4
  | none => false

def signedLoadShapeEvidenceMatches
    (result : Result aeneas_extract.ZiskInstExtract)
    (op width : _root_.Nat)
    (m32 : _root_.Bool) : _root_.Bool :=
  match proofRowShapeProjection result with
  | some row =>
      row.op == op
      && row.isExternalOp == true
      && row.m32 == m32
      && row.aSrc == 6
      && row.aUseSpImm1 == 0
      && row.aOffsetImm0 == 5
      && row.bSrc == 5
      && row.bUseSpImm1 == 0
      && row.bOffsetImm0 == 4096
      && row.store == 3
      && row.storeOffset == 3
      && row.storePc == false
      && row.setPc == false
      && row.indWidth == width
      && row.jmpOffset1 == 4
      && row.jmpOffset2 == 4
  | none => false

def branchShapeEvidenceMatches
    (result : Result aeneas_extract.ZiskInstExtract)
    (op : _root_.Nat)
    (jmpOffset1 jmpOffset2 : _root_.Int) : _root_.Bool :=
  match proofRowShapeProjection result with
  | some row =>
      row.op == op
      && row.isExternalOp == true
      && row.m32 == false
      && row.aSrc == 6
      && row.aUseSpImm1 == 0
      && row.aOffsetImm0 == 5
      && row.bSrc == 6
      && row.bUseSpImm1 == 0
      && row.bOffsetImm0 == 7
      && row.store == 0
      && row.storeOffset == 0
      && row.storePc == false
      && row.setPc == false
      && row.indWidth == 0
      && row.jmpOffset1 == jmpOffset1
      && row.jmpOffset2 == jmpOffset2
  | none => false

def mulShapeEvidenceMatches
    (result : Result aeneas_extract.ZiskInstExtract)
    (op : _root_.Nat)
    (m32 : _root_.Bool) : _root_.Bool :=
  match proofRowShapeProjection result with
  | some row =>
      row.op == op
      && row.isExternalOp == true
      && row.m32 == m32
      && row.aSrc == 6
      && row.aUseSpImm1 == 0
      && row.aOffsetImm0 == 5
      && row.bSrc == 6
      && row.bUseSpImm1 == 0
      && row.bOffsetImm0 == 7
      && row.store == 3
      && row.storeOffset == 3
      && row.storePc == false
      && row.setPc == false
      && row.indWidth == 0
      && row.jmpOffset1 == 4
      && row.jmpOffset2 == 4
  | none => false

def divRemShapeEvidenceMatches
    (result : Result aeneas_extract.ZiskInstExtract)
    (op : _root_.Nat)
    (m32 : _root_.Bool) : _root_.Bool :=
  match proofRowShapeProjection result with
  | some row =>
      row.op == op
      && row.isExternalOp == true
      && row.m32 == m32
      && row.aSrc == 6
      && row.aUseSpImm1 == 0
      && row.aOffsetImm0 == 5
      && row.bSrc == 6
      && row.bUseSpImm1 == 0
      && row.bOffsetImm0 == 7
      && row.store == 3
      && row.storeOffset == 3
      && row.storePc == false
      && row.setPc == false
      && row.indWidth == 0
      && row.jmpOffset1 == 4
      && row.jmpOffset2 == 4
  | none => false

def rawFenceAccepted (result : Result _root_.Bool) : _root_.Bool :=
  match result with
  | ok accepted => accepted
  | fail _ => false
  | div => false

def allConfiguredStartsReturnRows : Bool :=
EOF

  first=1
  for fn in "${rust_extract_fns[@]}"; do
    if [[ "$first" -eq 1 ]]; then
      printf '  rowReturned (aeneas_extract.%s sampleInst)\n' "$fn" >> "$lean_check/GeneratedChecks.lean"
      first=0
    else
      printf '  && rowReturned (aeneas_extract.%s sampleInst)\n' "$fn" >> "$lean_check/GeneratedChecks.lean"
    fi
  done

  cat >> "$lean_check/GeneratedChecks.lean" <<'EOF'

example : allConfiguredStartsReturnRows = true := by
  native_decide

example :
    rowModeMatches (aeneas_extract.extract_lui_from_inst sampleInst)
      1 false false false 2 2 3 4 4 = true := by
  native_decide

example :
    rowShapeMatches (aeneas_extract.extract_lui_from_inst sampleInst)
      (proofRowShape 16 1 2 0 0 2 0 4096 3 3 false false 0 4 4 false false) = true := by
  native_decide

example :
    luiRowModeEvidenceMatches (aeneas_extract.extract_lui_from_inst sampleInst) = true := by
  native_decide

example :
    rowModeMatches (aeneas_extract.extract_auipc_from_inst sampleInst)
      0 false false true 2 2 3 4 4096 = true := by
  native_decide

example :
    rowShapeMatches (aeneas_extract.extract_auipc_from_inst sampleInst)
      (proofRowShape 16 0 2 0 0 2 0 0 3 3 true false 0 4 4096 false false) = true := by
  native_decide

example :
    auipcRowModeEvidenceMatches (aeneas_extract.extract_auipc_from_inst sampleInst) = true := by
  native_decide

example :
    rowModeMatches (aeneas_extract.extract_jal_from_inst sampleInst)
      0 false false true 2 2 3 4096 4 = true := by
  native_decide

example :
    rowShapeMatches (aeneas_extract.extract_jal_from_inst sampleInst)
      (proofRowShape 16 0 2 0 0 2 0 0 3 3 true false 0 4096 4 false false) = true := by
  native_decide

example :
    jalRowModeEvidenceMatches (aeneas_extract.extract_jal_from_inst sampleInst) = true := by
  native_decide

example :
    jalrControlEvidenceMatches (aeneas_extract.extract_jalr_from_inst sampleInst) = true := by
  native_decide

example :
    rowModeMatches (aeneas_extract.extract_addw_from_inst sampleInst)
      26 true true false 6 6 3 4 4 = true := by
  native_decide

example :
    rowShapeMatches (aeneas_extract.extract_addw_from_inst sampleInst)
      (proofRowShape 16 26 6 0 5 6 0 7 3 3 false false 0 4 4 true true) = true := by
  native_decide

example :
    addwShapeEvidenceMatches (aeneas_extract.extract_addw_from_inst sampleInst) = true := by
  native_decide

example :
    rowModeMatches (aeneas_extract.extract_add_from_inst sampleInst)
      10 true false false 6 6 3 4 4 = true := by
  native_decide

example :
    rowShapeMatches (aeneas_extract.extract_add_from_inst sampleInst)
      (proofRowShape 16 10 6 0 5 6 0 7 3 3 false false 0 4 4 true false) = true := by
  native_decide

example :
    addViaBinaryShapeEvidenceMatches (aeneas_extract.extract_add_from_inst sampleInst) = true := by
  native_decide

example :
    rowModeMatches (aeneas_extract.extract_add_from_inst sampleRs1ZeroInst)
      1 false false false 2 6 3 4 4 = true := by
  native_decide

example :
    rowShapeMatches (aeneas_extract.extract_add_from_inst sampleRs1ZeroInst)
      (proofRowShape 16 1 2 0 0 6 0 7 3 3 false false 0 4 4 false false) = true := by
  native_decide

example :
    rowModeMatches (aeneas_extract.extract_addi_from_inst sampleInst)
      10 true false false 6 2 3 4 4 = true := by
  native_decide

example :
    rowShapeMatches (aeneas_extract.extract_addi_from_inst sampleInst)
      (proofRowShape 16 10 6 0 5 2 0 4096 3 3 false false 0 4 4 true false) = true := by
  native_decide

example :
    addiViaBinaryShapeEvidenceMatches (aeneas_extract.extract_addi_from_inst sampleInst) = true := by
  native_decide

example :
    rowShapeMatches (aeneas_extract.extract_sub_from_inst sampleInst)
      (proofRowShape 16 11 6 0 5 6 0 7 3 3 false false 0 4 4 true false) = true := by
  native_decide

example :
    subShapeEvidenceMatches (aeneas_extract.extract_sub_from_inst sampleInst) = true := by
  native_decide

example :
    rowShapeMatches (aeneas_extract.extract_subw_from_inst sampleInst)
      (proofRowShape 16 27 6 0 5 6 0 7 3 3 false false 0 4 4 true true) = true := by
  native_decide

example :
    subwShapeEvidenceMatches (aeneas_extract.extract_subw_from_inst sampleInst) = true := by
  native_decide

example :
    rowShapeMatches (aeneas_extract.extract_addiw_from_inst sampleInst)
      (proofRowShape 16 26 6 0 5 2 0 4096 3 3 false false 0 4 4 true true) = true := by
  native_decide

example :
    addiwShapeEvidenceMatches (aeneas_extract.extract_addiw_from_inst sampleInst) = true := by
  native_decide

example :
    rowShapeMatches (aeneas_extract.extract_and_from_inst sampleInst)
      (proofRowShape 16 14 6 0 5 6 0 7 3 3 false false 0 4 4 true false) = true := by
  native_decide

example :
    andShapeEvidenceMatches (aeneas_extract.extract_and_from_inst sampleInst) = true := by
  native_decide

example :
    rowShapeMatches (aeneas_extract.extract_or_from_inst sampleInst)
      (proofRowShape 16 15 6 0 5 6 0 7 3 3 false false 0 4 4 true false) = true := by
  native_decide

example :
    orShapeEvidenceMatches (aeneas_extract.extract_or_from_inst sampleInst) = true := by
  native_decide

example :
    rowShapeMatches (aeneas_extract.extract_xor_from_inst sampleInst)
      (proofRowShape 16 16 6 0 5 6 0 7 3 3 false false 0 4 4 true false) = true := by
  native_decide

example :
    xorShapeEvidenceMatches (aeneas_extract.extract_xor_from_inst sampleInst) = true := by
  native_decide

example :
    rowShapeMatches (aeneas_extract.extract_slt_from_inst sampleInst)
      (proofRowShape 16 7 6 0 5 6 0 7 3 3 false false 0 4 4 true false) = true := by
  native_decide

example :
    sltShapeEvidenceMatches (aeneas_extract.extract_slt_from_inst sampleInst) = true := by
  native_decide

example :
    rowShapeMatches (aeneas_extract.extract_sltu_from_inst sampleInst)
      (proofRowShape 16 6 6 0 5 6 0 7 3 3 false false 0 4 4 true false) = true := by
  native_decide

example :
    sltuShapeEvidenceMatches (aeneas_extract.extract_sltu_from_inst sampleInst) = true := by
  native_decide

example :
    rowShapeMatches (aeneas_extract.extract_andi_from_inst sampleInst)
      (proofRowShape 16 14 6 0 5 2 0 4096 3 3 false false 0 4 4 true false) = true := by
  native_decide

example :
    andiShapeEvidenceMatches (aeneas_extract.extract_andi_from_inst sampleInst) = true := by
  native_decide

example :
    rowShapeMatches (aeneas_extract.extract_ori_from_inst sampleInst)
      (proofRowShape 16 15 6 0 5 2 0 4096 3 3 false false 0 4 4 true false) = true := by
  native_decide

example :
    oriShapeEvidenceMatches (aeneas_extract.extract_ori_from_inst sampleInst) = true := by
  native_decide

example :
    rowShapeMatches (aeneas_extract.extract_xori_from_inst sampleInst)
      (proofRowShape 16 16 6 0 5 2 0 4096 3 3 false false 0 4 4 true false) = true := by
  native_decide

example :
    xoriShapeEvidenceMatches (aeneas_extract.extract_xori_from_inst sampleInst) = true := by
  native_decide

example :
    rowShapeMatches (aeneas_extract.extract_slti_from_inst sampleInst)
      (proofRowShape 16 7 6 0 5 2 0 4096 3 3 false false 0 4 4 true false) = true := by
  native_decide

example :
    sltiShapeEvidenceMatches (aeneas_extract.extract_slti_from_inst sampleInst) = true := by
  native_decide

example :
    rowShapeMatches (aeneas_extract.extract_sltiu_from_inst sampleInst)
      (proofRowShape 16 6 6 0 5 2 0 4096 3 3 false false 0 4 4 true false) = true := by
  native_decide

example :
    sltiuShapeEvidenceMatches (aeneas_extract.extract_sltiu_from_inst sampleInst) = true := by
  native_decide

example :
    rowShapeMatches (aeneas_extract.extract_sll_from_inst sampleInst)
      (proofRowShape 16 33 6 0 5 6 0 7 3 3 false false 0 4 4 true false) = true := by
  native_decide

example :
    sllShapeEvidenceMatches (aeneas_extract.extract_sll_from_inst sampleInst) = true := by
  native_decide

example :
    rowShapeMatches (aeneas_extract.extract_srl_from_inst sampleInst)
      (proofRowShape 16 34 6 0 5 6 0 7 3 3 false false 0 4 4 true false) = true := by
  native_decide

example :
    srlShapeEvidenceMatches (aeneas_extract.extract_srl_from_inst sampleInst) = true := by
  native_decide

example :
    rowShapeMatches (aeneas_extract.extract_sra_from_inst sampleInst)
      (proofRowShape 16 35 6 0 5 6 0 7 3 3 false false 0 4 4 true false) = true := by
  native_decide

example :
    sraShapeEvidenceMatches (aeneas_extract.extract_sra_from_inst sampleInst) = true := by
  native_decide

example :
    rowShapeMatches (aeneas_extract.extract_slli_from_inst sampleInst)
      (proofRowShape 16 33 6 0 5 2 0 4096 3 3 false false 0 4 4 true false) = true := by
  native_decide

example :
    slliShapeEvidenceMatches (aeneas_extract.extract_slli_from_inst sampleInst) = true := by
  native_decide

example :
    rowShapeMatches (aeneas_extract.extract_srli_from_inst sampleInst)
      (proofRowShape 16 34 6 0 5 2 0 4096 3 3 false false 0 4 4 true false) = true := by
  native_decide

example :
    srliShapeEvidenceMatches (aeneas_extract.extract_srli_from_inst sampleInst) = true := by
  native_decide

example :
    rowShapeMatches (aeneas_extract.extract_srai_from_inst sampleInst)
      (proofRowShape 16 35 6 0 5 2 0 4096 3 3 false false 0 4 4 true false) = true := by
  native_decide

example :
    sraiShapeEvidenceMatches (aeneas_extract.extract_srai_from_inst sampleInst) = true := by
  native_decide

example :
    rowShapeMatches (aeneas_extract.extract_sllw_from_inst sampleInst)
      (proofRowShape 16 36 6 0 5 6 0 7 3 3 false false 0 4 4 true true) = true := by
  native_decide

example :
    sllwShapeEvidenceMatches (aeneas_extract.extract_sllw_from_inst sampleInst) = true := by
  native_decide

example :
    rowShapeMatches (aeneas_extract.extract_srlw_from_inst sampleInst)
      (proofRowShape 16 37 6 0 5 6 0 7 3 3 false false 0 4 4 true true) = true := by
  native_decide

example :
    srlwShapeEvidenceMatches (aeneas_extract.extract_srlw_from_inst sampleInst) = true := by
  native_decide

example :
    rowShapeMatches (aeneas_extract.extract_sraw_from_inst sampleInst)
      (proofRowShape 16 38 6 0 5 6 0 7 3 3 false false 0 4 4 true true) = true := by
  native_decide

example :
    srawShapeEvidenceMatches (aeneas_extract.extract_sraw_from_inst sampleInst) = true := by
  native_decide

example :
    rowShapeMatches (aeneas_extract.extract_slliw_from_inst sampleInst)
      (proofRowShape 16 36 6 0 5 2 0 4096 3 3 false false 0 4 4 true true) = true := by
  native_decide

example :
    slliwShapeEvidenceMatches (aeneas_extract.extract_slliw_from_inst sampleInst) = true := by
  native_decide

example :
    rowShapeMatches (aeneas_extract.extract_srliw_from_inst sampleInst)
      (proofRowShape 16 37 6 0 5 2 0 4096 3 3 false false 0 4 4 true true) = true := by
  native_decide

example :
    srliwShapeEvidenceMatches (aeneas_extract.extract_srliw_from_inst sampleInst) = true := by
  native_decide

example :
    rowShapeMatches (aeneas_extract.extract_sraiw_from_inst sampleInst)
      (proofRowShape 16 38 6 0 5 2 0 4096 3 3 false false 0 4 4 true true) = true := by
  native_decide

example :
    sraiwShapeEvidenceMatches (aeneas_extract.extract_sraiw_from_inst sampleInst) = true := by
  native_decide

example :
    rowShapeMatches (aeneas_extract.extract_sb_from_inst sampleInst)
      (proofRowShape 16 1 6 0 5 6 0 7 2 4096 false false 1 4 4 false false) = true := by
  native_decide

example :
    storeShapeEvidenceMatches (aeneas_extract.extract_sb_from_inst sampleInst) 1 = true := by
  native_decide

example :
    rowShapeMatches (aeneas_extract.extract_sh_from_inst sampleInst)
      (proofRowShape 16 1 6 0 5 6 0 7 2 4096 false false 2 4 4 false false) = true := by
  native_decide

example :
    storeShapeEvidenceMatches (aeneas_extract.extract_sh_from_inst sampleInst) 2 = true := by
  native_decide

example :
    rowShapeMatches (aeneas_extract.extract_sw_from_inst sampleInst)
      (proofRowShape 16 1 6 0 5 6 0 7 2 4096 false false 4 4 4 false false) = true := by
  native_decide

example :
    storeShapeEvidenceMatches (aeneas_extract.extract_sw_from_inst sampleInst) 4 = true := by
  native_decide

example :
    rowShapeMatches (aeneas_extract.extract_sd_from_inst sampleInst)
      (proofRowShape 16 1 6 0 5 6 0 7 2 4096 false false 8 4 4 false false) = true := by
  native_decide

example :
    storeShapeEvidenceMatches (aeneas_extract.extract_sd_from_inst sampleInst) 8 = true := by
  native_decide

example :
    rowShapeMatches (aeneas_extract.extract_ld_from_inst sampleInst)
      (proofRowShape 16 1 6 0 5 5 0 4096 3 3 false false 8 4 4 false false) = true := by
  native_decide

example :
    loadShapeEvidenceMatches (aeneas_extract.extract_ld_from_inst sampleInst) 8 = true := by
  native_decide

example :
    rowShapeMatches (aeneas_extract.extract_lbu_from_inst sampleInst)
      (proofRowShape 16 1 6 0 5 5 0 4096 3 3 false false 1 4 4 false false) = true := by
  native_decide

example :
    loadShapeEvidenceMatches (aeneas_extract.extract_lbu_from_inst sampleInst) 1 = true := by
  native_decide

example :
    rowShapeMatches (aeneas_extract.extract_lhu_from_inst sampleInst)
      (proofRowShape 16 1 6 0 5 5 0 4096 3 3 false false 2 4 4 false false) = true := by
  native_decide

example :
    loadShapeEvidenceMatches (aeneas_extract.extract_lhu_from_inst sampleInst) 2 = true := by
  native_decide

example :
    rowShapeMatches (aeneas_extract.extract_lwu_from_inst sampleInst)
      (proofRowShape 16 1 6 0 5 5 0 4096 3 3 false false 4 4 4 false false) = true := by
  native_decide

example :
    loadShapeEvidenceMatches (aeneas_extract.extract_lwu_from_inst sampleInst) 4 = true := by
  native_decide

example :
    rowShapeMatches (aeneas_extract.extract_lb_from_inst sampleInst)
      (proofRowShape 16 39 6 0 5 5 0 4096 3 3 false false 1 4 4 true false) = true := by
  native_decide

example :
    signedLoadShapeEvidenceMatches (aeneas_extract.extract_lb_from_inst sampleInst) 39 1 false = true := by
  native_decide

example :
    rowShapeMatches (aeneas_extract.extract_lh_from_inst sampleInst)
      (proofRowShape 16 40 6 0 5 5 0 4096 3 3 false false 2 4 4 true false) = true := by
  native_decide

example :
    signedLoadShapeEvidenceMatches (aeneas_extract.extract_lh_from_inst sampleInst) 40 2 false = true := by
  native_decide

example :
    rowShapeMatches (aeneas_extract.extract_lw_from_inst sampleInst)
      (proofRowShape 16 41 6 0 5 5 0 4096 3 3 false false 4 4 4 true true) = true := by
  native_decide

example :
    signedLoadShapeEvidenceMatches (aeneas_extract.extract_lw_from_inst sampleInst) 41 4 true = true := by
  native_decide

example :
    rowShapeMatches (aeneas_extract.extract_beq_from_inst sampleInst)
      (proofRowShape 16 9 6 0 5 6 0 7 0 0 false false 0 4096 4 true false) = true := by
  native_decide

example :
    branchShapeEvidenceMatches (aeneas_extract.extract_beq_from_inst sampleInst) 9 4096 4 = true := by
  native_decide

example :
    rowShapeMatches (aeneas_extract.extract_bne_from_inst sampleInst)
      (proofRowShape 16 9 6 0 5 6 0 7 0 0 false false 0 4 4096 true false) = true := by
  native_decide

example :
    branchShapeEvidenceMatches (aeneas_extract.extract_bne_from_inst sampleInst) 9 4 4096 = true := by
  native_decide

example :
    rowShapeMatches (aeneas_extract.extract_blt_from_inst sampleInst)
      (proofRowShape 16 7 6 0 5 6 0 7 0 0 false false 0 4096 4 true false) = true := by
  native_decide

example :
    branchShapeEvidenceMatches (aeneas_extract.extract_blt_from_inst sampleInst) 7 4096 4 = true := by
  native_decide

example :
    rowShapeMatches (aeneas_extract.extract_bge_from_inst sampleInst)
      (proofRowShape 16 7 6 0 5 6 0 7 0 0 false false 0 4 4096 true false) = true := by
  native_decide

example :
    branchShapeEvidenceMatches (aeneas_extract.extract_bge_from_inst sampleInst) 7 4 4096 = true := by
  native_decide

example :
    rowShapeMatches (aeneas_extract.extract_bltu_from_inst sampleInst)
      (proofRowShape 16 6 6 0 5 6 0 7 0 0 false false 0 4096 4 true false) = true := by
  native_decide

example :
    branchShapeEvidenceMatches (aeneas_extract.extract_bltu_from_inst sampleInst) 6 4096 4 = true := by
  native_decide

example :
    rowShapeMatches (aeneas_extract.extract_bgeu_from_inst sampleInst)
      (proofRowShape 16 6 6 0 5 6 0 7 0 0 false false 0 4 4096 true false) = true := by
  native_decide

example :
    branchShapeEvidenceMatches (aeneas_extract.extract_bgeu_from_inst sampleInst) 6 4 4096 = true := by
  native_decide

example :
    rowShapeMatches (aeneas_extract.extract_mul_from_inst sampleInst)
      (proofRowShape 16 180 6 0 5 6 0 7 3 3 false false 0 4 4 true false) = true := by
  native_decide

example :
    mulShapeEvidenceMatches (aeneas_extract.extract_mul_from_inst sampleInst) 180 false = true := by
  native_decide

example :
    rowShapeMatches (aeneas_extract.extract_mulh_from_inst sampleInst)
      (proofRowShape 16 181 6 0 5 6 0 7 3 3 false false 0 4 4 true false) = true := by
  native_decide

example :
    mulShapeEvidenceMatches (aeneas_extract.extract_mulh_from_inst sampleInst) 181 false = true := by
  native_decide

example :
    rowShapeMatches (aeneas_extract.extract_mulhu_from_inst sampleInst)
      (proofRowShape 16 177 6 0 5 6 0 7 3 3 false false 0 4 4 true false) = true := by
  native_decide

example :
    mulShapeEvidenceMatches (aeneas_extract.extract_mulhu_from_inst sampleInst) 177 false = true := by
  native_decide

example :
    rowShapeMatches (aeneas_extract.extract_mulhsu_from_inst sampleInst)
      (proofRowShape 16 179 6 0 5 6 0 7 3 3 false false 0 4 4 true false) = true := by
  native_decide

example :
    mulShapeEvidenceMatches (aeneas_extract.extract_mulhsu_from_inst sampleInst) 179 false = true := by
  native_decide

example :
    rowShapeMatches (aeneas_extract.extract_mulw_from_inst sampleInst)
      (proofRowShape 16 182 6 0 5 6 0 7 3 3 false false 0 4 4 true true) = true := by
  native_decide

example :
    mulShapeEvidenceMatches (aeneas_extract.extract_mulw_from_inst sampleInst) 182 true = true := by
  native_decide

example :
    rowShapeMatches (aeneas_extract.extract_div_from_inst sampleInst)
      (proofRowShape 16 186 6 0 5 6 0 7 3 3 false false 0 4 4 true false) = true := by
  native_decide

example :
    divRemShapeEvidenceMatches (aeneas_extract.extract_div_from_inst sampleInst) 186 false = true := by
  native_decide

example :
    rowShapeMatches (aeneas_extract.extract_divu_from_inst sampleInst)
      (proofRowShape 16 184 6 0 5 6 0 7 3 3 false false 0 4 4 true false) = true := by
  native_decide

example :
    divRemShapeEvidenceMatches (aeneas_extract.extract_divu_from_inst sampleInst) 184 false = true := by
  native_decide

example :
    rowShapeMatches (aeneas_extract.extract_divw_from_inst sampleInst)
      (proofRowShape 16 190 6 0 5 6 0 7 3 3 false false 0 4 4 true true) = true := by
  native_decide

example :
    divRemShapeEvidenceMatches (aeneas_extract.extract_divw_from_inst sampleInst) 190 true = true := by
  native_decide

example :
    rowShapeMatches (aeneas_extract.extract_divuw_from_inst sampleInst)
      (proofRowShape 16 188 6 0 5 6 0 7 3 3 false false 0 4 4 true true) = true := by
  native_decide

example :
    divRemShapeEvidenceMatches (aeneas_extract.extract_divuw_from_inst sampleInst) 188 true = true := by
  native_decide

example :
    rowShapeMatches (aeneas_extract.extract_rem_from_inst sampleInst)
      (proofRowShape 16 187 6 0 5 6 0 7 3 3 false false 0 4 4 true false) = true := by
  native_decide

example :
    divRemShapeEvidenceMatches (aeneas_extract.extract_rem_from_inst sampleInst) 187 false = true := by
  native_decide

example :
    rowShapeMatches (aeneas_extract.extract_remu_from_inst sampleInst)
      (proofRowShape 16 185 6 0 5 6 0 7 3 3 false false 0 4 4 true false) = true := by
  native_decide

example :
    divRemShapeEvidenceMatches (aeneas_extract.extract_remu_from_inst sampleInst) 185 false = true := by
  native_decide

example :
    rowShapeMatches (aeneas_extract.extract_remw_from_inst sampleInst)
      (proofRowShape 16 191 6 0 5 6 0 7 3 3 false false 0 4 4 true true) = true := by
  native_decide

example :
    divRemShapeEvidenceMatches (aeneas_extract.extract_remw_from_inst sampleInst) 191 true = true := by
  native_decide

example :
    rowShapeMatches (aeneas_extract.extract_remuw_from_inst sampleInst)
      (proofRowShape 16 189 6 0 5 6 0 7 3 3 false false 0 4 4 true true) = true := by
  native_decide

example :
    divRemShapeEvidenceMatches (aeneas_extract.extract_remuw_from_inst sampleInst) 189 true = true := by
  native_decide

example :
    rawFenceAccepted (aeneas_extract.extract_fence_accepts_raw_inst 0x0000000F#u32) = true := by
  native_decide

example :
    rawFenceAccepted (aeneas_extract.extract_fence_accepts_raw_inst 0x1000000F#u32) = false := by
  native_decide

example :
    rowShapeMatches (aeneas_extract.extract_fence_from_inst sampleInst)
      (proofRowShape 16 0 2 0 0 2 0 0 0 0 false false 0 4 4 false false) = true := by
  native_decide

example :
    fencePinsEvidenceMatches (aeneas_extract.extract_fence_from_inst sampleInst) = true := by
  native_decide

example :
    rawDecodeSupported (aeneas_extract.extract_decode_rv64im_raw 0x00b50533#u32) = true := by
  native_decide

example :
    rawDecodeOpcodeId (aeneas_extract.extract_decode_rv64im_raw 0x00b50533#u32) = 6 := by
  native_decide

example :
    rawSupported (aeneas_extract.extract_rv64im_opcode_supported 0x00b50533#u32) = true := by
  native_decide

example :
    rawTranspileAccepted (aeneas_extract.extract_transpile_rv64im_raw 0x00b50533#u32) = true := by
  native_decide

example :
    rawTranspileAcceptedFlag (aeneas_extract.extract_transpile_rv64im_accepted_raw 0x00b50533#u32) = true := by
  native_decide

example :
    rawTranspileMaterializedFlag
      (aeneas_extract.extract_transpile_rv64im_materializes_raw 0x00b50533#u32) = true := by
  native_decide

example :
    rawTranspileRowBSrc (aeneas_extract.extract_transpile_rv64im_raw 0x00b50533#u32) = 6 := by
  native_decide

example :
    rawTranspileRowBOffset (aeneas_extract.extract_transpile_rv64im_raw 0x00b50533#u32) = 11 := by
  native_decide

EOF

  rv64im_raw_cases=(
    "lui 0x123451B7 1"
    "auipc 0x12345197 2"
    "jal 0x100001EF 3"
    "jalr 0x100281E7 4"
    "fence 0x0000000F 5"
    "add 0x007281B3 6"
    "sub 0x407281B3 7"
    "sll 0x007291B3 8"
    "slt 0x0072A1B3 9"
    "sltu 0x0072B1B3 10"
    "xor 0x0072C1B3 11"
    "srl 0x0072D1B3 12"
    "sra 0x4072D1B3 13"
    "or 0x0072E1B3 14"
    "and 0x0072F1B3 15"
    "addw 0x007281BB 16"
    "subw 0x407281BB 17"
    "sllw 0x007291BB 18"
    "srlw 0x0072D1BB 19"
    "sraw 0x4072D1BB 20"
    "mul 0x027281B3 21"
    "mulh 0x027291B3 22"
    "mulhsu 0x0272A1B3 23"
    "mulhu 0x0272B1B3 24"
    "mulw 0x027281BB 25"
    "div 0x0272C1B3 26"
    "divu 0x0272D1B3 27"
    "divw 0x0272C1BB 28"
    "divuw 0x0272D1BB 29"
    "rem 0x0272E1B3 30"
    "remu 0x0272F1B3 31"
    "remw 0x0272E1BB 32"
    "remuw 0x0272F1BB 33"
    "addi 0x12328193 34"
    "slli 0x00729193 35"
    "slti 0x1232A193 36"
    "sltiu 0x1232B193 37"
    "xori 0x1232C193 38"
    "srli 0x0072D193 39"
    "srai 0x4072D193 40"
    "ori 0x1232E193 41"
    "andi 0x1232F193 42"
    "addiw 0x1232819B 43"
    "slliw 0x0072919B 44"
    "srliw 0x0072D19B 45"
    "sraiw 0x4072D19B 46"
    "beq 0x10728063 47"
    "bne 0x10729063 48"
    "blt 0x1072C063 49"
    "bge 0x1072D063 50"
    "bltu 0x1072E063 51"
    "bgeu 0x1072F063 52"
    "lb 0x02028183 53"
    "lbu 0x0202C183 54"
    "lh 0x02029183 55"
    "lhu 0x0202D183 56"
    "lw 0x0202A183 57"
    "lwu 0x0202E183 58"
    "ld 0x0202B183 59"
    "sb 0x02728023 60"
    "sh 0x02729023 61"
    "sw 0x0272A023 62"
    "sd 0x0272B023 63"
  )

  {
    echo
    echo "-- Representative raw encodings for the current 63-opcode RV64IM surface."
    for case in "${rv64im_raw_cases[@]}"; do
      read -r name raw opcode_id <<<"$case"
      cat <<EOF_CASE

example :
    rawDecodeOpcodeId (aeneas_extract.extract_decode_rv64im_raw ${raw}#u32) = ${opcode_id} := by
  native_decide

example :
    rawTranspileAccepted (aeneas_extract.extract_transpile_rv64im_raw ${raw}#u32) = true := by
  native_decide

example :
    rawTranspileAcceptedFlag (aeneas_extract.extract_transpile_rv64im_accepted_raw ${raw}#u32) = true := by
  native_decide

example :
    rawTranspileMaterializedFlag
      (aeneas_extract.extract_transpile_rv64im_materializes_raw ${raw}#u32) = true := by
  native_decide

example :
    KnownZiskDecodeGapRaw ${raw}#u32 = false := by
  native_decide

example :
    KnownZiskRowMaterializationGapRaw ${raw}#u32 = false := by
  native_decide

example :
    KnownZiskGapRaw ${raw}#u32 = false := by
  native_decide
EOF_CASE
    done
  } >> "$lean_check/GeneratedChecks.lean"

  rv64im_branch_cases=(
    "add_rs1_zero_copy_rs2 0x007001B3 6"
    "add_rs2_zero_copy_rs1 0x000281B3 6"
    "or_rs1_zero_copy_rs2 0x007061B3 14"
    "or_rs2_zero_copy_rs1 0x0002E1B3 14"
    "addi_zero_zero_zero_nop 0x00000013 34"
    "addi_rd_zero_nonzero_hint 0x00128013 34"
    "addi_imm_zero_copy_rs1 0x00028193 34"
    "addiw_zero_zero_zero_nop 0x0000001B 43"
  )

  {
    echo
    echo "-- Additional raw encodings for branchy lowering paths inside covered opcodes."
    for case in "${rv64im_branch_cases[@]}"; do
      read -r name raw opcode_id <<<"$case"
      cat <<EOF_CASE

example :
    rawDecodeOpcodeId (aeneas_extract.extract_decode_rv64im_raw ${raw}#u32) = ${opcode_id} := by
  native_decide

example :
    rawTranspileAccepted (aeneas_extract.extract_transpile_rv64im_raw ${raw}#u32) = true := by
  native_decide

example :
    rawTranspileAcceptedFlag (aeneas_extract.extract_transpile_rv64im_accepted_raw ${raw}#u32) = true := by
  native_decide

example :
    rawTranspileMaterializedFlag
      (aeneas_extract.extract_transpile_rv64im_materializes_raw ${raw}#u32) = true := by
  native_decide

example :
    KnownZiskDecodeGapRaw ${raw}#u32 = false := by
  native_decide

example :
    KnownZiskRowMaterializationGapRaw ${raw}#u32 = false := by
  native_decide

example :
    KnownZiskGapRaw ${raw}#u32 = false := by
  native_decide
EOF_CASE
    done
  } >> "$lean_check/GeneratedChecks.lean"

  raw_hex_u32() {
    printf '0x%08X#u32' "$(($1 & 0xffffffff))"
  }

  rv_r_raw() {
    echo $((($1 << 25) | ($2 << 20) | ($3 << 15) | ($4 << 12) | ($5 << 7) | $6))
  }

  rv_i_raw() {
    local imm=$(( $1 & 0xfff ))
    echo $(((imm << 20) | ($2 << 15) | ($3 << 12) | ($4 << 7) | $5))
  }

  rv_s_raw() {
    local imm=$(( $1 & 0xfff ))
    echo $((((imm >> 5) << 25) | ($2 << 20) | ($3 << 15) | ($4 << 12) | ((imm & 0x1f) << 7) | 0x23))
  }

  rv_b_raw() {
    local imm=$(( $1 & 0x1fff ))
    echo $(((((imm >> 12) & 1) << 31) | (((imm >> 5) & 0x3f) << 25) | ($2 << 20) | ($3 << 15) | ($4 << 12) | (((imm >> 1) & 0xf) << 8) | (((imm >> 11) & 1) << 7) | 0x63))
  }

  rv_u_raw() {
    echo $((($1 & 0xfffff000) | ($2 << 7) | $3))
  }

  rv_j_raw() {
    local imm=$(( $1 & 0x1fffff ))
    echo $(((((imm >> 20) & 1) << 31) | (((imm >> 1) & 0x3ff) << 21) | (((imm >> 11) & 1) << 20) | (((imm >> 12) & 0xff) << 12) | ($2 << 7) | 0x6f))
  }

  {
    echo
    echo "-- Small shape-grid raw encodings for broader extracted-Lean materialization coverage."
    echo "def rawShapeGridCaseOk (raw : Std.U32) : Bool :="
    echo "  rawDecodeSupported (aeneas_extract.extract_decode_rv64im_raw raw) &&"
    echo "  rawTranspileAccepted (aeneas_extract.extract_transpile_rv64im_raw raw) &&"
    echo "  rawTranspileAcceptedFlag (aeneas_extract.extract_transpile_rv64im_accepted_raw raw) &&"
    echo "  rawTranspileMaterializedFlag"
    echo "    (aeneas_extract.extract_transpile_rv64im_materializes_raw raw) &&"
    echo "  !KnownZiskGapRaw raw"
    echo
    echo "def rawShapeGridCases : List Std.U32 := ["

    first=1
    emit_shape_raw() {
      local raw="$1"
      if [[ "$first" -eq 1 ]]; then
        printf '  %s' "$(raw_hex_u32 "$raw")"
        first=0
      else
        printf ',\n  %s' "$(raw_hex_u32 "$raw")"
      fi
    }

    regs=(0 5 31)
    i_imms=(-1 0 1)
    s_imms=(-4 0 4)
    b_imms=(-4 0 4)
    u_imms=(0 0x80000000)
    j_imms=(-4 0 4)
    shift64=(0 63)
    shift32=(0 31)
    r_ops=(
      "0 0 0x33" "32 0 0x33" "0 1 0x33" "0 2 0x33" "0 3 0x33"
      "0 4 0x33" "0 5 0x33" "32 5 0x33" "0 6 0x33" "0 7 0x33"
      "0 0 0x3b" "32 0 0x3b" "0 1 0x3b" "0 5 0x3b" "32 5 0x3b"
      "1 0 0x33" "1 1 0x33" "1 2 0x33" "1 3 0x33" "1 0 0x3b"
      "1 4 0x33" "1 5 0x33" "1 4 0x3b" "1 5 0x3b" "1 6 0x33"
      "1 7 0x33" "1 6 0x3b" "1 7 0x3b"
    )

    for op in "${r_ops[@]}"; do
      read -r funct7 funct3 opcode <<<"$op"
      for rd in "${regs[@]}"; do
        for rs1 in "${regs[@]}"; do
          for rs2 in "${regs[@]}"; do
            emit_shape_raw "$(rv_r_raw "$funct7" "$rs2" "$rs1" "$funct3" "$rd" "$opcode")"
          done
        done
      done
    done

    for rd in "${regs[@]}"; do
      for imm in "${u_imms[@]}"; do
        emit_shape_raw "$(rv_u_raw "$imm" "$rd" 0x37)"
        emit_shape_raw "$(rv_u_raw "$imm" "$rd" 0x17)"
      done
      for imm in "${j_imms[@]}"; do
        emit_shape_raw "$(rv_j_raw "$imm" "$rd")"
      done
      for rs1 in "${regs[@]}"; do
        for imm in "${i_imms[@]}"; do
          emit_shape_raw "$(rv_i_raw "$imm" "$rs1" 0 "$rd" 0x67)"
          emit_shape_raw "$(rv_i_raw "$imm" "$rs1" 0 "$rd" 0x13)"
          emit_shape_raw "$(rv_i_raw "$imm" "$rs1" 2 "$rd" 0x13)"
          emit_shape_raw "$(rv_i_raw "$imm" "$rs1" 3 "$rd" 0x13)"
          emit_shape_raw "$(rv_i_raw "$imm" "$rs1" 4 "$rd" 0x13)"
          emit_shape_raw "$(rv_i_raw "$imm" "$rs1" 6 "$rd" 0x13)"
          emit_shape_raw "$(rv_i_raw "$imm" "$rs1" 7 "$rd" 0x13)"
          emit_shape_raw "$(rv_i_raw "$imm" "$rs1" 0 "$rd" 0x1b)"
          emit_shape_raw "$(rv_i_raw "$imm" "$rs1" 0 "$rd" 0x03)"
          emit_shape_raw "$(rv_i_raw "$imm" "$rs1" 1 "$rd" 0x03)"
          emit_shape_raw "$(rv_i_raw "$imm" "$rs1" 2 "$rd" 0x03)"
          emit_shape_raw "$(rv_i_raw "$imm" "$rs1" 3 "$rd" 0x03)"
          emit_shape_raw "$(rv_i_raw "$imm" "$rs1" 4 "$rd" 0x03)"
          emit_shape_raw "$(rv_i_raw "$imm" "$rs1" 5 "$rd" 0x03)"
          emit_shape_raw "$(rv_i_raw "$imm" "$rs1" 6 "$rd" 0x03)"
        done
        for shamt in "${shift64[@]}"; do
          emit_shape_raw "$(rv_i_raw "$shamt" "$rs1" 1 "$rd" 0x13)"
          emit_shape_raw "$(rv_i_raw "$shamt" "$rs1" 5 "$rd" 0x13)"
          emit_shape_raw "$(rv_i_raw "$((0x400 | shamt))" "$rs1" 5 "$rd" 0x13)"
        done
        for shamt in "${shift32[@]}"; do
          emit_shape_raw "$(rv_i_raw "$shamt" "$rs1" 1 "$rd" 0x1b)"
          emit_shape_raw "$(rv_i_raw "$shamt" "$rs1" 5 "$rd" 0x1b)"
          emit_shape_raw "$(rv_i_raw "$((0x400 | shamt))" "$rs1" 5 "$rd" 0x1b)"
        done
      done
    done

    for rs1 in "${regs[@]}"; do
      for rs2 in "${regs[@]}"; do
        for imm in "${b_imms[@]}"; do
          emit_shape_raw "$(rv_b_raw "$imm" "$rs2" "$rs1" 0)"
          emit_shape_raw "$(rv_b_raw "$imm" "$rs2" "$rs1" 1)"
          emit_shape_raw "$(rv_b_raw "$imm" "$rs2" "$rs1" 4)"
          emit_shape_raw "$(rv_b_raw "$imm" "$rs2" "$rs1" 5)"
          emit_shape_raw "$(rv_b_raw "$imm" "$rs2" "$rs1" 6)"
          emit_shape_raw "$(rv_b_raw "$imm" "$rs2" "$rs1" 7)"
        done
        for imm in "${s_imms[@]}"; do
          emit_shape_raw "$(rv_s_raw "$imm" "$rs2" "$rs1" 0)"
          emit_shape_raw "$(rv_s_raw "$imm" "$rs2" "$rs1" 1)"
          emit_shape_raw "$(rv_s_raw "$imm" "$rs2" "$rs1" 2)"
          emit_shape_raw "$(rv_s_raw "$imm" "$rs2" "$rs1" 3)"
        done
      done
    done

    for pred in 0 15; do
      for succ in 0 15; do
        emit_shape_raw "$(((pred << 24) | (succ << 20) | 0x0f))"
      done
    done

    echo
    echo "]"
    echo
    echo "example : rawShapeGridCases.all rawShapeGridCaseOk = true := by"
    echo "  native_decide"
  } >> "$lean_check/GeneratedChecks.lean"

  if [[ "$AENEAS_CHECK_RV_WIDE_SHAPES" != 0 ]]; then
    cat >> "$lean_check/GeneratedChecks.lean" <<'EOF'

/-!
Optional wide extracted-Lean shape check.

This is disabled by default because it asks `native_decide` to run the
extracted production decode/lowering/materialization path for the broad
register/edge-immediate grid below. It is still finite and reproducible, but
currently costs several minutes; a measured run on the development machine was
about 202s for `GeneratedChecks`, 170s for `RvCompleteness`, and 6m21s
end-to-end.
-/

def rawOfNat32 (n : Nat) : Std.U32 :=
  ⟨BitVec.ofNat 32 n⟩

def rawRType (funct7 rs2 rs1 funct3 rd opcode : Nat) : Std.U32 :=
  rawOfNat32
    ((funct7 <<< 25) ||| (rs2 <<< 20) ||| (rs1 <<< 15) |||
      (funct3 <<< 12) ||| (rd <<< 7) ||| opcode)

def allRvRegs : List Nat :=
  List.range 32

def allRTypeOpcodeShapes : List (Nat × Nat × Nat) := [
  (0, 0, 0x33),  (32, 0, 0x33), (0, 1, 0x33),  (0, 2, 0x33),
  (0, 3, 0x33),  (0, 4, 0x33),  (0, 5, 0x33),  (32, 5, 0x33),
  (0, 6, 0x33),  (0, 7, 0x33),  (0, 0, 0x3b),  (32, 0, 0x3b),
  (0, 1, 0x3b),  (0, 5, 0x3b),  (32, 5, 0x3b), (1, 0, 0x33),
  (1, 1, 0x33),  (1, 2, 0x33),  (1, 3, 0x33),  (1, 0, 0x3b),
  (1, 4, 0x33),  (1, 5, 0x33),  (1, 4, 0x3b),  (1, 5, 0x3b),
  (1, 6, 0x33),  (1, 7, 0x33),  (1, 6, 0x3b),  (1, 7, 0x3b)
]

def allRTypeRegisterShapes (caseOk : Std.U32 → Bool) : Bool :=
  allRTypeOpcodeShapes.all fun (funct7, funct3, opcode) =>
    allRvRegs.all fun rd =>
      allRvRegs.all fun rs1 =>
        allRvRegs.all fun rs2 =>
          caseOk (rawRType funct7 rs2 rs1 funct3 rd opcode)

def allRTypeRegisterShapesMaterialize : Bool :=
  allRTypeRegisterShapes rawShapeGridCaseOk

theorem allRTypeRegisterShapesMaterialize_ok :
    allRTypeRegisterShapesMaterialize = true := by
  native_decide

def rawIType (imm rs1 funct3 rd opcode : Nat) : Std.U32 :=
  rawOfNat32
    (((imm % 4096) <<< 20) ||| (rs1 <<< 15) |||
      (funct3 <<< 12) ||| (rd <<< 7) ||| opcode)

def edgeIImmediates : List Nat := [
  2048, -- -2048 sign-extended through the 12-bit immediate field
  4095, -- -1
  0,
  1,
  2047
]

def allITypeRegisterEdgeImmediates (caseOk : Std.U32 → Bool) : Bool :=
  allRvRegs.all fun rd =>
    allRvRegs.all fun rs1 =>
      edgeIImmediates.all fun imm =>
        caseOk (rawIType imm rs1 0 rd 0x67) && -- jalr
        caseOk (rawIType imm rs1 0 rd 0x13) && -- addi
        caseOk (rawIType imm rs1 2 rd 0x13) && -- slti
        caseOk (rawIType imm rs1 3 rd 0x13) && -- sltiu
        caseOk (rawIType imm rs1 4 rd 0x13) && -- xori
        caseOk (rawIType imm rs1 6 rd 0x13) && -- ori
        caseOk (rawIType imm rs1 7 rd 0x13) && -- andi
        caseOk (rawIType imm rs1 0 rd 0x1b) && -- addiw
        caseOk (rawIType imm rs1 0 rd 0x03) && -- lb
        caseOk (rawIType imm rs1 1 rd 0x03) && -- lh
        caseOk (rawIType imm rs1 2 rd 0x03) && -- lw
        caseOk (rawIType imm rs1 3 rd 0x03) && -- ld
        caseOk (rawIType imm rs1 4 rd 0x03) && -- lbu
        caseOk (rawIType imm rs1 5 rd 0x03) && -- lhu
        caseOk (rawIType imm rs1 6 rd 0x03)    -- lwu

def allITypeRegisterEdgeImmediatesMaterialize : Bool :=
  allITypeRegisterEdgeImmediates rawShapeGridCaseOk

def shift64Amounts : List Nat :=
  List.range 64

def shift32Amounts : List Nat :=
  List.range 32

def allShiftRegisterShapes (caseOk : Std.U32 → Bool) : Bool :=
  allRvRegs.all fun rd =>
    allRvRegs.all fun rs1 =>
      (shift64Amounts.all fun shamt =>
        caseOk (rawIType shamt rs1 1 rd 0x13) &&
        caseOk (rawIType shamt rs1 5 rd 0x13) &&
        caseOk (rawIType (0x400 ||| shamt) rs1 5 rd 0x13)) &&
      (shift32Amounts.all fun shamt =>
        caseOk (rawIType shamt rs1 1 rd 0x1b) &&
        caseOk (rawIType shamt rs1 5 rd 0x1b) &&
        caseOk (rawIType (0x400 ||| shamt) rs1 5 rd 0x1b))

def allShiftRegisterShapesMaterialize : Bool :=
  allShiftRegisterShapes rawShapeGridCaseOk

theorem allITypeRegisterEdgeImmediatesMaterialize_ok :
    allITypeRegisterEdgeImmediatesMaterialize = true := by
  native_decide

theorem allShiftRegisterShapesMaterialize_ok :
    allShiftRegisterShapesMaterialize = true := by
  native_decide

def rawSType (imm rs2 rs1 funct3 : Nat) : Std.U32 :=
  let imm12 := imm % 4096
  rawOfNat32
    (((imm12 >>> 5) <<< 25) ||| (rs2 <<< 20) ||| (rs1 <<< 15) |||
      (funct3 <<< 12) ||| ((imm12 &&& 0x1f) <<< 7) ||| 0x23)

def rawBType (imm rs2 rs1 funct3 : Nat) : Std.U32 :=
  let imm13 := imm % 8192
  rawOfNat32
    ((((imm13 >>> 12) &&& 1) <<< 31) |||
      (((imm13 >>> 5) &&& 0x3f) <<< 25) |||
      (rs2 <<< 20) ||| (rs1 <<< 15) ||| (funct3 <<< 12) |||
      (((imm13 >>> 1) &&& 0xf) <<< 8) |||
      (((imm13 >>> 11) &&& 1) <<< 7) ||| 0x63)

def rawUType (imm rd opcode : Nat) : Std.U32 :=
  rawOfNat32 ((imm &&& 0xfffff000) ||| (rd <<< 7) ||| opcode)

def rawJType (imm rd : Nat) : Std.U32 :=
  let imm21 := imm % 2097152
  rawOfNat32
    ((((imm21 >>> 20) &&& 1) <<< 31) |||
      (((imm21 >>> 1) &&& 0x3ff) <<< 21) |||
      (((imm21 >>> 11) &&& 1) <<< 20) |||
      (((imm21 >>> 12) &&& 0xff) <<< 12) ||| (rd <<< 7) ||| 0x6f)

def edgeSImmediates : List Nat := [
  2048, -- -2048 sign-extended through the 12-bit immediate field
  4088, -- -8
  0,
  7,
  2047
]

def edgeBImmediates : List Nat := [
  4096, -- -4096 sign-extended through the 13-bit immediate field
  8188, -- -4
  0,
  4,
  4094
]

def edgeUImmediates : List Nat := [
  0,
  0x1000,
  0x7ffff000,
  0x80000000,
  0xfffff000
]

def edgeJImmediates : List Nat := [
  1048576, -- -1048576 sign-extended through the 21-bit immediate field
  2097148, -- -4
  0,
  4,
  1048574
]

def allStoreRegisterEdgeImmediates (caseOk : Std.U32 → Bool) : Bool :=
  allRvRegs.all fun rs1 =>
    allRvRegs.all fun rs2 =>
      edgeSImmediates.all fun imm =>
        caseOk (rawSType imm rs2 rs1 0) &&
        caseOk (rawSType imm rs2 rs1 1) &&
        caseOk (rawSType imm rs2 rs1 2) &&
        caseOk (rawSType imm rs2 rs1 3)

def allStoreRegisterEdgeImmediatesMaterialize : Bool :=
  allStoreRegisterEdgeImmediates rawShapeGridCaseOk

def allBranchRegisterEdgeImmediates (caseOk : Std.U32 → Bool) : Bool :=
  allRvRegs.all fun rs1 =>
    allRvRegs.all fun rs2 =>
      edgeBImmediates.all fun imm =>
        caseOk (rawBType imm rs2 rs1 0) &&
        caseOk (rawBType imm rs2 rs1 1) &&
        caseOk (rawBType imm rs2 rs1 4) &&
        caseOk (rawBType imm rs2 rs1 5) &&
        caseOk (rawBType imm rs2 rs1 6) &&
        caseOk (rawBType imm rs2 rs1 7)

def allBranchRegisterEdgeImmediatesMaterialize : Bool :=
  allBranchRegisterEdgeImmediates rawShapeGridCaseOk

def allUpperAndJumpEdgeImmediates (caseOk : Std.U32 → Bool) : Bool :=
  allRvRegs.all fun rd =>
    (edgeUImmediates.all fun imm =>
      caseOk (rawUType imm rd 0x37) &&
      caseOk (rawUType imm rd 0x17)) &&
    (edgeJImmediates.all fun imm =>
      caseOk (rawJType imm rd))

def allUpperAndJumpEdgeImmediatesMaterialize : Bool :=
  allUpperAndJumpEdgeImmediates rawShapeGridCaseOk

def allFencePredSuccShapes (caseOk : Std.U32 → Bool) : Bool :=
  (List.range 16).all fun pred =>
    (List.range 16).all fun succ =>
      caseOk (rawOfNat32 ((pred <<< 24) ||| (succ <<< 20) ||| 0x0f))

def allFencePredSuccShapesMaterialize : Bool :=
  allFencePredSuccShapes rawShapeGridCaseOk

theorem allStoreRegisterEdgeImmediatesMaterialize_ok :
    allStoreRegisterEdgeImmediatesMaterialize = true := by
  native_decide

theorem allBranchRegisterEdgeImmediatesMaterialize_ok :
    allBranchRegisterEdgeImmediatesMaterialize = true := by
  native_decide

theorem allUpperAndJumpEdgeImmediatesMaterialize_ok :
    allUpperAndJumpEdgeImmediatesMaterialize = true := by
  native_decide

theorem allFencePredSuccShapesMaterialize_ok :
    allFencePredSuccShapesMaterialize = true := by
  native_decide

def allWideRvShapeFamiliesMaterialize : Bool :=
  allRTypeRegisterShapesMaterialize &&
  allITypeRegisterEdgeImmediatesMaterialize &&
  allShiftRegisterShapesMaterialize &&
  allStoreRegisterEdgeImmediatesMaterialize &&
  allBranchRegisterEdgeImmediatesMaterialize &&
  allUpperAndJumpEdgeImmediatesMaterialize &&
  allFencePredSuccShapesMaterialize

def allExhaustiveRvShapeFamiliesMaterialize : Bool :=
  allRTypeRegisterShapesMaterialize &&
  allShiftRegisterShapesMaterialize &&
  allFencePredSuccShapesMaterialize

def allEdgeRvShapeFamiliesMaterialize : Bool :=
  allITypeRegisterEdgeImmediatesMaterialize &&
  allStoreRegisterEdgeImmediatesMaterialize &&
  allBranchRegisterEdgeImmediatesMaterialize &&
  allUpperAndJumpEdgeImmediatesMaterialize

theorem allWideRvShapeFamiliesMaterialize_ok :
    allWideRvShapeFamiliesMaterialize = true := by
  simp [allWideRvShapeFamiliesMaterialize,
    allRTypeRegisterShapesMaterialize_ok,
    allITypeRegisterEdgeImmediatesMaterialize_ok,
    allShiftRegisterShapesMaterialize_ok,
    allStoreRegisterEdgeImmediatesMaterialize_ok,
    allBranchRegisterEdgeImmediatesMaterialize_ok,
    allUpperAndJumpEdgeImmediatesMaterialize_ok,
    allFencePredSuccShapesMaterialize_ok]

theorem allExhaustiveRvShapeFamiliesMaterialize_ok :
    allExhaustiveRvShapeFamiliesMaterialize = true := by
  simp [allExhaustiveRvShapeFamiliesMaterialize,
    allRTypeRegisterShapesMaterialize_ok,
    allShiftRegisterShapesMaterialize_ok,
    allFencePredSuccShapesMaterialize_ok]

theorem allEdgeRvShapeFamiliesMaterialize_ok :
    allEdgeRvShapeFamiliesMaterialize = true := by
  simp [allEdgeRvShapeFamiliesMaterialize,
    allITypeRegisterEdgeImmediatesMaterialize_ok,
    allStoreRegisterEdgeImmediatesMaterialize_ok,
    allBranchRegisterEdgeImmediatesMaterialize_ok,
    allUpperAndJumpEdgeImmediatesMaterialize_ok]
EOF
  fi

  cat >> "$lean_check/GeneratedChecks.lean" <<'EOF'

end zisk_core_generated_checks
EOF

  if [[ "$AENEAS_CHECK_FENCE_COMPLETENESS" != 0 ]]; then
    cat > "$lean_check/FenceCompleteness.lean" <<'EOF'
import ProductionM2

open Aeneas Aeneas.Std Result
open zisk_core

namespace zisk_core_generated_fence_completeness

def fenceTsoWord : Std.U32 := 0x8330000F#u32

def fenceOpcode (inst : Std.U32) : Result Std.U32 := do
  let masked ← lift (inst &&& 0x7F#u32)
  ok masked

def fenceFunct3 (inst : Std.U32) : Result Std.U32 := do
  let masked ← lift (inst &&& 0x7000#u32)
  masked >>> 12#i32

def SailGenericFenceEncoding (inst : Std.U32) : Prop :=
  inst ≠ fenceTsoWord ∧
  fenceOpcode inst = ok 0x0F#u32 ∧
  fenceFunct3 inst = ok 0#u32

def resultU32Eq (result : Result Std.U32) (expected : Std.U32) : Bool :=
  match result with
  | ok actual => actual == expected
  | fail _ => false
  | div => false

def SailGenericFenceEncodingBool (inst : Std.U32) : Bool :=
  inst != fenceTsoWord &&
    resultU32Eq (fenceOpcode inst) 0x0F#u32 &&
    resultU32Eq (fenceFunct3 inst) 0#u32

def rawTranspileAccepted (result : Result aeneas_extract.Rv64imTranspileExtract) : Bool :=
  match result with
  | ok summary => summary.accepted
  | fail _ => false
  | div => false

def rawDecodeSupported (result : Result aeneas_extract.Rv64imDecodeExtract) : Bool :=
  match result with
  | ok decoded => decoded.supported
  | fail _ => false
  | div => false

def rawFenceAccepted (result : Result Bool) : Bool :=
  match result with
  | ok accepted => accepted
  | fail _ => false
  | div => false

def ExtractedRawFenceDecodeCompletenessBool : Prop :=
  ∀ raw, SailGenericFenceEncodingBool raw = true →
    rawDecodeSupported (aeneas_extract.extract_decode_rv64im_raw raw) = true

def ExtractedRawFenceGateCompletenessBool : Prop :=
  ∀ raw, SailGenericFenceEncodingBool raw = true →
    rawFenceAccepted (aeneas_extract.extract_fence_accepts_raw_inst raw) = true

def ExtractedRawFenceCompletenessBool : Prop :=
  ∀ raw, SailGenericFenceEncodingBool raw = true →
    rawTranspileAccepted (aeneas_extract.extract_transpile_rv64im_raw raw) = true

def genericFenceWithFm : Std.U32 := 0x1000000F#u32

-- Concrete counterexample diagnostics. Keep commented out when we want the
-- build error to show the direct generic completeness proof obligation.
--
-- theorem generic_fence_with_fm_has_spec_shape :
--     SailGenericFenceEncodingBool genericFenceWithFm = true := by
--   native_decide
--
-- theorem extracted_raw_fence_counterexample :
--     rawTranspileAccepted
--       (aeneas_extract.extract_transpile_rv64im_raw genericFenceWithFm) = false := by
--   native_decide

theorem extracted_raw_fence_decode_completeness :
    ExtractedRawFenceDecodeCompletenessBool := by
  intro raw h_sail
  simp [rawDecodeSupported,
    SailGenericFenceEncodingBool,
    resultU32Eq,
    fenceOpcode,
    fenceFunct3] at h_sail ⊢

-- Fence-specific gate completeness. This is downstream of the general
-- extracted decode theorem above, so keep it commented while inspecting the
-- first natural failure stage.
--
-- theorem extracted_raw_fence_gate_completeness :
--     ExtractedRawFenceGateCompletenessBool := by
--   intro raw h_sail
--   simp [rawFenceAccepted,
--     aeneas_extract.extract_fence_accepts_raw_inst,
--     aeneas_extract.fence_decode.decode_fence_raw,
--     aeneas_extract.fence_decode.FenceDecodeKind.Insts.CoreCmpPartialEqFenceDecodeKind.eq,
--     SailGenericFenceEncodingBool,
--     resultU32Eq,
--     fenceOpcode,
--     fenceFunct3] at h_sail ⊢

-- Downstream full-transpiler completeness. This is implied only after the
-- decoder-gate theorem above, so keep it commented while inspecting the
-- narrower decoder failure.
--
-- theorem extracted_raw_fence_completeness :
--     ExtractedRawFenceCompletenessBool := by
--   intro raw h_sail
--   simp [rawTranspileAccepted,
--     aeneas_extract.extract_transpile_rv64im_raw,
--     SailGenericFenceEncodingBool,
--     resultU32Eq,
--     fenceOpcode,
--     fenceFunct3] at h_sail ⊢

end zisk_core_generated_fence_completeness
EOF
    nix develop "$ROOT" --command bash -lc 'cd "$1" && lake build ProductionM2 GeneratedChecks FenceCompleteness' bash "$lean_check"
  elif [[ "$AENEAS_CHECK_RV_COMPLETENESS" != 0 ]]; then
    cat > "$lean_check/RvCompleteness.lean" <<'EOF'
import ProductionM2
import GeneratedChecks

open Aeneas Aeneas.Std Result
open zisk_core

namespace zisk_core_generated_rv_completeness

/-!
This module is the RV-completeness harness, distinct from Clean circuit
`GeneralFormalCircuit.Completeness`.

The target statement is:

  every raw RV instruction accepted by Sail's decoder is accepted by the
  Aeneas-extracted production ZisK decode/transpile path and maps to a
  covered circuit/equivalence opcode.

This generated Aeneas check is parameterized over the Sail executability
predicate. The intended instantiation is Sail's `ext_decode`/execute model;
that bridge is kept outside this Aeneas workspace because the pinned Aeneas
Lean runtime and the current generated Sail-Lean tree use different Lean
toolchains.
-/

def rawDecodeSupported (result : Result aeneas_extract.Rv64imDecodeExtract) : Bool :=
  match result with
  | ok decoded => decoded.supported
  | fail _ => false
  | div => false

def rawDecodeOpcodeId (result : Result aeneas_extract.Rv64imDecodeExtract) : Nat :=
  match result with
  | ok decoded => decoded.opcode_id.val
  | fail _ => 0
  | div => 0

def rawTranspileAccepted (result : Result aeneas_extract.Rv64imTranspileExtract) : Bool :=
  match result with
  | ok summary => summary.accepted
  | fail _ => false
  | div => false

def rawTranspileAcceptedFlag (result : Result Bool) : Bool :=
  match result with
  | ok accepted => accepted
  | fail _ => false
  | div => false

def rawTranspileMaterializedFlag (result : Result Bool) : Bool :=
  match result with
  | ok materialized => materialized
  | fail _ => false
  | div => false

def resultU32Eq (result : Result Std.U32) (expected : Std.U32) : Bool :=
  match result with
  | ok actual => actual == expected
  | fail _ => false
  | div => false

def rawOpcode (raw : Std.U32) : Result Std.U32 := do
  let masked ← lift (raw &&& 0x7F#u32)
  ok masked

def rawFunct3 (raw : Std.U32) : Result Std.U32 := do
  let masked ← lift (raw &&& 0x7000#u32)
  masked >>> 12#i32

def rawRd (raw : Std.U32) : Result Std.U32 := do
  let masked ← lift (raw &&& 0xF80#u32)
  masked >>> 7#i32

def rawRs1 (raw : Std.U32) : Result Std.U32 := do
  let masked ← lift (raw &&& 0xF8000#u32)
  masked >>> 15#i32

/-- ZisK production decoder support, from Aeneas-extracted production code. -/
def ZiskDecodeSupportedRaw (raw : Std.U32) : Prop :=
  rawDecodeSupported (aeneas_extract.extract_decode_rv64im_raw raw) = true

/-- ZisK production lowering/transpile acceptance, from Aeneas extraction. -/
def ZiskTranspileAcceptedRaw (raw : Std.U32) : Prop :=
  rawTranspileAccepted (aeneas_extract.extract_transpile_rv64im_raw raw) = true

/-- ZisK production lowering support without row materialization. -/
def ZiskLowerableRaw (raw : Std.U32) : Prop :=
  rawTranspileAcceptedFlag (aeneas_extract.extract_transpile_rv64im_accepted_raw raw) = true

/-- The extracted production lowering path actually emitted a row. -/
def ZiskRowMaterializedRaw (raw : Std.U32) : Prop :=
  rawTranspileMaterializedFlag
    (aeneas_extract.extract_transpile_rv64im_materializes_raw raw) = true

/-- Current known decode gap: Sail accepts generic FENCE-shaped raw words that
the production ZisK decoder rejects. This predicate is intentionally defined
from raw instruction fields plus the extracted ZisK decoder result, so it can
be removed when ZisK's FENCE decoder is broadened. -/
def KnownZiskDecodeGapRaw (raw : Std.U32) : Bool :=
  resultU32Eq (rawOpcode raw) 0x0F#u32 &&
  resultU32Eq (rawFunct3 raw) 0#u32 &&
  !(rawDecodeSupported (aeneas_extract.extract_decode_rv64im_raw raw))

/-- Extracted production lowering/materialization gap. This is deliberately
definition-based rather than hand-enumerated: if the extracted production
decoder accepts a raw instruction but the extracted production lowering path
does not emit a row, the raw word is outside the avoiding-known-bugs theorem
until the row-builder proof is closed or the production issue is fixed. -/
def KnownZiskRowMaterializationGapRaw (raw : Std.U32) : Bool :=
  rawDecodeSupported (aeneas_extract.extract_decode_rv64im_raw raw) &&
  !(rawTranspileMaterializedFlag
      (aeneas_extract.extract_transpile_rv64im_materializes_raw raw))

def KnownZiskGapRaw (raw : Std.U32) : Bool :=
  KnownZiskDecodeGapRaw raw || KnownZiskRowMaterializationGapRaw raw

/-- Current covered opcode-id surface. IDs are assigned by the extracted
`opcode_id` wrapper and are checked by the generated representative examples
in `GeneratedChecks.lean`. ID 1000 is the FENCE generic/unsupported marker. -/
def coveredOpcodeId (opcodeId : Nat) : Bool :=
  1 <= opcodeId && opcodeId <= 63

/-- Circuit/equivalence coverage predicate for a raw word. -/
def ZiskCircuitCoveredRaw (raw : Std.U32) : Prop :=
  ZiskDecodeSupportedRaw raw ∧
  ZiskLowerableRaw raw ∧
  ZiskRowMaterializedRaw raw ∧
  coveredOpcodeId (rawDecodeOpcodeId (aeneas_extract.extract_decode_rv64im_raw raw)) = true

def rawOfNat32 (n : Nat) : Std.U32 :=
  ⟨BitVec.ofNat 32 n⟩

def rawRType (funct7 rs2 rs1 funct3 rd opcode : Nat) : Std.U32 :=
  rawOfNat32
    ((funct7 <<< 25) ||| (rs2 <<< 20) ||| (rs1 <<< 15) |||
      (funct3 <<< 12) ||| (rd <<< 7) ||| opcode)

def allRvRegs : List Nat :=
  List.range 32

/-- Boolean counterpart of ADD raw-shape circuit coverage. This is deliberately
defined from the Aeneas-extracted production raw decoder/lowering wrappers. -/
def AddRawShapeCircuitCoveredBool (raw : Std.U32) : Bool :=
  rawDecodeSupported (aeneas_extract.extract_decode_rv64im_raw raw) &&
  (rawDecodeOpcodeId (aeneas_extract.extract_decode_rv64im_raw raw) == 6) &&
  rawTranspileAccepted (aeneas_extract.extract_transpile_rv64im_raw raw) &&
  rawTranspileAcceptedFlag (aeneas_extract.extract_transpile_rv64im_accepted_raw raw) &&
  rawTranspileMaterializedFlag
    (aeneas_extract.extract_transpile_rv64im_materializes_raw raw) &&
  !KnownZiskGapRaw raw

def allAddRawShapesCircuitCovered : Bool :=
  allRvRegs.all fun rd =>
    allRvRegs.all fun rs1 =>
      allRvRegs.all fun rs2 =>
        AddRawShapeCircuitCoveredBool (rawRType 0 rs2 rs1 0 rd 0x33)

theorem allAddRawShapesCircuitCovered_ok :
    allAddRawShapesCircuitCovered = true := by
  native_decide

def RvAvoidKnownBugsFor (sailExecutableRaw : Std.U32 → Prop) : Prop :=
  ∀ raw, sailExecutableRaw raw → KnownZiskGapRaw raw = false → ZiskDecodeSupportedRaw raw

def RvLoweringCompleteness : Prop :=
  ∀ raw, ZiskDecodeSupportedRaw raw → ZiskLowerableRaw raw

def RvRowMaterializationCompleteness : Prop :=
  ∀ raw, ZiskLowerableRaw raw → ZiskRowMaterializedRaw raw

def RvOpcodeCoverageCompleteness : Prop :=
  ∀ raw, ZiskDecodeSupportedRaw raw →
    coveredOpcodeId (rawDecodeOpcodeId (aeneas_extract.extract_decode_rv64im_raw raw)) = true

def RvCompletenessFor (sailExecutableRaw : Std.U32 → Prop) : Prop :=
  ∀ raw, sailExecutableRaw raw → ZiskCircuitCoveredRaw raw

def RvCompletenessAvoidingKnownBugsFor (sailExecutableRaw : Std.U32 → Prop) : Prop :=
  ∀ raw, sailExecutableRaw raw → KnownZiskGapRaw raw = false → ZiskCircuitCoveredRaw raw

/-- Empty extraction context used by builder-total lemmas. The production
`aeneas_extract.extract_transpile_rv64im_materializes_raw` wrapper uses this
same shape before calling `lower_rv64im_single_row_input`. -/
def emptyExtractContext : riscv2zisk_context.Riscv2ZiskContext :=
  {
    extract_inst := none,
    extract_marker := (),
    input_precompile := none,
    output_precompile := none,
    input_precompile_reg := none,
    output_precompile_reg := none
  }

def helperMaterializesResult
    (f : riscv2zisk_context.Riscv2ZiskContext →
      Result riscv2zisk_context.Riscv2ZiskContext) : Result Bool := do
  let ctx ← f emptyExtractContext
  ok ctx.extract_inst.isSome

def helperMaterializesResultFlag
    (f : riscv2zisk_context.Riscv2ZiskContext →
      Result riscv2zisk_context.Riscv2ZiskContext) : Bool :=
  match helperMaterializesResult f with
  | ok true => true
  | _ => false

def builderOkFlag (result : Result zisk_inst_builder.ZiskInstBuilder) : Bool :=
  match result with
  | ok _ => true
  | _ => false

/-- First structural row-builder-total lemma. FENCE lowers through production
`nop`, so this closes the helper used by the current known-good FENCE surface
without relying on finite raw-word enumeration. -/
theorem empty_nop_materializes_result
    (i : riscv2zisk_single_row.Rv64imLoweringInput) :
    helperMaterializesResult (fun ctx => ctx.nop i 4#u64) = ok true := by
  simp [helperMaterializesResult, emptyExtractContext,
    riscv2zisk_context.Riscv2ZiskContext.nop,
    zisk_inst_builder.ZiskInstBuilder.new_for_rv64im_lowering,
    zisk_inst_builder.ZiskInstBuilder.new,
    zisk_inst_builder.ZiskInstBuilder.Insts.CoreDefaultDefault.default,
    zisk_inst.ZiskInst.Insts.CoreDefaultDefault.default,
    zisk_inst_builder.ZiskInstBuilder.src_a_imm,
    zisk_inst_builder.ZiskInstBuilder.src_b_imm,
    zisk_inst_builder.ZiskInstBuilder.op_zisk,
    zisk_ops.ZiskOp.op_type,
    zisk_ops.ZiskOp.code,
    zisk_ops.ZiskOp.input_size,
    zisk_ops.ZiskOp.is_m32,
    zisk_inst.ZiskOperationType.Insts.CoreConvertFromOpType.from,
    zisk_inst_builder.ZiskInstBuilder.set_runtime_op_fields,
    zisk_inst_builder.ZiskInstBuilder.j,
    zisk_inst_builder.ZiskInstBuilder.build,
    riscv2zisk_context.Riscv2ZiskContext.insert_inst]
  rfl

theorem one_u64_ne_zero : ¬ ((1#u64 : Std.U64) = 0#u64) := by
  native_decide

theorem one_u64_not_lt_regs_from :
    ¬ ((1#u64 : Std.U64) < (UScalar.cast .U64 zisk_registers.REGS_IN_MAIN_FROM)) := by
  native_decide

theorem regs_to_not_lt_one_u64 :
    ¬ ((UScalar.cast .U64 zisk_registers.REGS_IN_MAIN_TO) < (1#u64 : Std.U64)) := by
  native_decide

theorem one_i64_ne_zero : ¬ ((1#i64 : Std.I64) = 0#i64) := by
  native_decide

theorem one_i64_not_lt_regs_from :
    ¬ ((1#i64 : Std.I64) < (UScalar.hcast .I64 zisk_registers.REGS_IN_MAIN_FROM)) := by
  native_decide

theorem regs_to_not_lt_one_i64 :
    ¬ ((UScalar.hcast .I64 zisk_registers.REGS_IN_MAIN_TO) < (1#i64 : Std.I64)) := by
  native_decide

theorem one_u64_scalar_ne_zero : ¬ ((1#64#uscalar : Std.U64) = 0#u64) := by
  native_decide

theorem one_u64_scalar_not_lt_regs_from_set_width :
    ¬ ((1#64#uscalar : Std.U64) <
      (BitVec.setWidth 64 1#System.Platform.numBits#uscalar : Std.U64)) := by
  native_decide

theorem regs_to_set_width_not_lt_one_u64_scalar :
    ¬ ((BitVec.setWidth 64 31#System.Platform.numBits#uscalar : Std.U64) <
      (1#64#uscalar : Std.U64)) := by
  native_decide

theorem one_i64_scalar_ne_zero : ¬ ((1#64#iscalar : Std.I64) = 0#i64) := by
  native_decide

theorem i64_zero_eq_zero : (0#64#iscalar : Std.I64) = 0#i64 := by
  native_decide

theorem u64_zero_eq_zero : (0#64#uscalar : Std.U64) = 0#u64 := by
  native_decide

theorem u64_one_val_ne_zero : ¬ ((↑(1#64#uscalar : Std.U64) : Nat) = 0) := by
  native_decide

theorem u64_one_val_not_gt_regs_to : ¬ (31 < (↑(1#64#uscalar : Std.U64) : Nat)) := by
  native_decide

theorem u64_31_ne_zero : ¬ ((31#64#uscalar : Std.U64) = 0#u64) := by
  native_decide

theorem u64_31_val_ne_zero : ¬ ((↑(31#64#uscalar : Std.U64) : Nat) = 0) := by
  native_decide

theorem u64_31_val_not_gt_regs_to : ¬ (31 < (↑(31#64#uscalar : Std.U64) : Nat)) := by
  native_decide

theorem i64_one_val_not_lt_regs_from : ¬ ((↑(1#64#iscalar : Std.I64) : Int) < 1) := by
  native_decide

theorem i64_one_val_not_gt_regs_to : ¬ (31 < (↑(1#64#iscalar : Std.I64) : Int)) := by
  native_decide

theorem i64_31_ne_zero : ¬ ((31#64#iscalar : Std.I64) = 0#i64) := by
  native_decide

theorem i64_31_val_not_lt_regs_from : ¬ ((↑(31#64#iscalar : Std.I64) : Int) < 1) := by
  native_decide

theorem i64_31_val_not_gt_regs_to : ¬ (31 < (↑(31#64#iscalar : Std.I64) : Int)) := by
  native_decide

theorem one_i64_scalar_not_lt_regs_from_set_width :
    ¬ ((1#64#iscalar : Std.I64) <
      (BitVec.setWidth 64 1#System.Platform.numBits#iscalar : Std.I64)) := by
  native_decide

theorem regs_to_set_width_not_lt_one_i64_scalar :
    ¬ ((BitVec.setWidth 64 31#System.Platform.numBits#iscalar : Std.I64) <
      (1#64#iscalar : Std.I64)) := by
  native_decide

theorem one_u64_val_not_lt_regs_from_set_width :
    ¬ ((↑(1#64#uscalar : Std.U64) : Nat) <
      (↑(BitVec.setWidth 64 1#System.Platform.numBits#uscalar : Std.U64) : Nat)) := by
  native_decide

theorem regs_to_set_width_val_not_lt_one_u64 :
    ¬ ((↑(BitVec.setWidth 64 31#System.Platform.numBits#uscalar : Std.U64) : Nat) <
      (↑(1#64#uscalar : Std.U64) : Nat)) := by
  native_decide

theorem one_i64_val_not_lt_regs_from_set_width :
    ¬ ((↑(1#64#iscalar : Std.I64) : Int) <
      (↑(BitVec.setWidth 64 1#System.Platform.numBits#iscalar : Std.I64) : Int)) := by
  native_decide

theorem regs_to_set_width_val_not_lt_one_i64 :
    ¬ ((↑(BitVec.setWidth 64 31#System.Platform.numBits#iscalar : Std.I64) : Int) <
      (↑(1#64#iscalar : Std.I64) : Int)) := by
  native_decide

theorem one_nat_not_lt_regs_from_set_width :
    ¬ (1 < (↑(BitVec.setWidth 64 1#System.Platform.numBits#uscalar : Std.U64) : Nat)) := by
  native_decide

theorem regs_to_set_width_nat_ne_zero :
    ¬ ((↑(BitVec.setWidth 64 31#System.Platform.numBits#uscalar : Std.U64) : Nat) = 0) := by
  native_decide

theorem regs_from_set_width_u64_val_eq :
    (↑(BitVec.setWidth 64 1#System.Platform.numBits#uscalar : Std.U64) : Nat) = 1 := by
  native_decide

theorem regs_to_set_width_u64_val_eq :
    (↑(BitVec.setWidth 64 31#System.Platform.numBits#uscalar : Std.U64) : Nat) = 31 := by
  native_decide

theorem two_nat_not_lt_regs_from_set_width :
    ¬ (2 < (↑(BitVec.setWidth 64 1#System.Platform.numBits#uscalar : Std.U64) : Nat)) := by
  native_decide

theorem regs_to_set_width_nat_not_le_one :
    ¬ ((↑(BitVec.setWidth 64 31#System.Platform.numBits#uscalar : Std.U64) : Nat) ≤ 1) := by
  native_decide

theorem one_int_not_lt_regs_from_set_width :
    ¬ (1 < (↑(BitVec.setWidth 64 1#System.Platform.numBits#iscalar : Std.I64) : Int)) := by
  native_decide

theorem regs_to_set_width_int_not_lt_one :
    ¬ ((↑(BitVec.setWidth 64 31#System.Platform.numBits#iscalar : Std.I64) : Int) < 1) := by
  native_decide

theorem regs_from_set_width_i64_val_eq :
    (↑(BitVec.setWidth 64 1#System.Platform.numBits#iscalar : Std.I64) : Int) = 1 := by
  native_decide

theorem regs_to_set_width_i64_val_eq :
    (↑(BitVec.setWidth 64 31#System.Platform.numBits#iscalar : Std.I64) : Int) = 31 := by
  native_decide

theorem two_int_not_lt_regs_from_set_width :
    ¬ (2 < (↑(BitVec.setWidth 64 1#System.Platform.numBits#iscalar : Std.I64) : Int)) := by
  native_decide

theorem regs_to_set_width_int_not_lt_two :
    ¬ ((↑(BitVec.setWidth 64 31#System.Platform.numBits#iscalar : Std.I64) : Int) < 2) := by
  native_decide

theorem u64_1_eq_pattern : (1#u64 : Std.U64) = (1#64#uscalar : Std.U64) := by
  apply UScalar.eq_of_val_eq
  native_decide

theorem u64_2_eq_pattern : (2#u64 : Std.U64) = (2#64#uscalar : Std.U64) := by
  apply UScalar.eq_of_val_eq
  native_decide

theorem u64_4_eq_pattern : (4#u64 : Std.U64) = (4#64#uscalar : Std.U64) := by
  apply UScalar.eq_of_val_eq
  native_decide

theorem u64_8_eq_pattern : (8#u64 : Std.U64) = (8#64#uscalar : Std.U64) := by
  apply UScalar.eq_of_val_eq
  native_decide

theorem i32_32_nonnegative : (32#i32 : Std.I32).val ≥ 0 := by
  native_decide

theorem i32_32_toNat_lt_u64_numBits :
    (32#i32 : Std.I32).toNat < UScalarTy.U64.numBits := by
  native_decide

theorem uscalar64_shift_right_i32_32_ok_true (x : Std.U64) :
    (do
      let _ ← x >>> 32#i32
      ok true) = ok true := by
  simp only [HShiftRight.hShiftRight,
    UScalar.shiftRight_IScalar,
    UScalar.shiftRight,
    i32_32_nonnegative,
    i32_32_toNat_lt_u64_numBits,
    Bind.bind,
    Std.bind,
    ↓reduceIte]

def allRvU64Regs : List Std.U64 :=
  [0#u64, 1#u64, 2#u64, 3#u64, 4#u64, 5#u64, 6#u64, 7#u64,
   8#u64, 9#u64, 10#u64, 11#u64, 12#u64, 13#u64, 14#u64, 15#u64,
   16#u64, 17#u64, 18#u64, 19#u64, 20#u64, 21#u64, 22#u64, 23#u64,
   24#u64, 25#u64, 26#u64, 27#u64, 28#u64, 29#u64, 30#u64, 31#u64]

def allRvU32Regs : List Std.U32 :=
  [0#u32, 1#u32, 2#u32, 3#u32, 4#u32, 5#u32, 6#u32, 7#u32,
   8#u32, 9#u32, 10#u32, 11#u32, 12#u32, 13#u32, 14#u32, 15#u32,
   16#u32, 17#u32, 18#u32, 19#u32, 20#u32, 21#u32, 22#u32, 23#u32,
   24#u32, 25#u32, 26#u32, 27#u32, 28#u32, 29#u32, 30#u32, 31#u32]

def edgeRvU32Regs : List Std.U32 := [0#u32, 1#u32, 31#u32]

theorem src_a_imm_zero_flag
    (zib : zisk_inst_builder.ZiskInstBuilder) :
    builderOkFlag
      (zisk_inst_builder.ZiskInstBuilder.src_a_imm zib 0#u64) = true := by
  have h_shift := uscalar64_shift_right_i32_32_ok_true (0#u64 : Std.U64)
  simp [builderOkFlag,
    zisk_inst_builder.ZiskInstBuilder.src_a_imm,
    lift] at h_shift ⊢
  cases h : ((0#u64 : Std.U64) >>> 32#i32) <;> simp [h] at h_shift ⊢

theorem src_b_imm_zero_flag
    (zib : zisk_inst_builder.ZiskInstBuilder) :
    builderOkFlag
      (zisk_inst_builder.ZiskInstBuilder.src_b_imm zib 0#u64) = true := by
  have h_shift := uscalar64_shift_right_i32_32_ok_true (0#u64 : Std.U64)
  simp [builderOkFlag,
    zisk_inst_builder.ZiskInstBuilder.src_b_imm,
    lift] at h_shift ⊢
  cases h : ((0#u64 : Std.U64) >>> 32#i32) <;> simp [h] at h_shift ⊢

theorem src_b_imm_zero_ok_true
    (zib : zisk_inst_builder.ZiskInstBuilder) :
    (match do
      let _ ← zisk_inst_builder.ZiskInstBuilder.src_b_imm zib 0#u64
      ok true with
    | ok true => true
    | _ => false) = true := by
  have h := src_b_imm_zero_flag zib
  simpa [builderOkFlag] using h

def allRvI64Regs : List Std.I64 :=
  [0#i64, 1#i64, 2#i64, 3#i64, 4#i64, 5#i64, 6#i64, 7#i64,
   8#i64, 9#i64, 10#i64, 11#i64, 12#i64, 13#i64, 14#i64, 15#i64,
   16#i64, 17#i64, 18#i64, 19#i64, 20#i64, 21#i64, 22#i64, 23#i64,
   24#i64, 25#i64, 26#i64, 27#i64, 28#i64, 29#i64, 30#i64, 31#i64]

/-- Non-enumerative row-builder-total milestone: with opcode/register routing
fixed, production ADDI materializes a row for every extracted signed
immediate. This keeps the immediate symbolic and exposes the remaining
row-materialization work as finite routing/opcode case splits plus similar
helper-total lemmas. -/
theorem empty_addi_reg1_materializes_result
    (imm : Std.I32) :
    helperMaterializesResult
      (fun ctx =>
        riscv2zisk_context.Riscv2ZiskContext.immediate_op_typed
          ctx
          { rom_address := 0#u64, rd := 1#u32, rs1 := 1#u32,
            rs2 := 0#u32, imm := imm }
          zisk_ops.ZiskOp.Add 4#u64) = ok true := by
  simp [helperMaterializesResult, emptyExtractContext,
    riscv2zisk_context.Riscv2ZiskContext.immediate_op_typed,
    zisk_inst_builder.ZiskInstBuilder.new_for_rv64im_lowering,
    zisk_inst_builder.ZiskInstBuilder.new,
    zisk_inst_builder.ZiskInstBuilder.Insts.CoreDefaultDefault.default,
    zisk_inst.ZiskInst.Insts.CoreDefaultDefault.default,
    zisk_inst_builder.ZiskInstBuilder.src_a_reg,
    zisk_inst_builder.ZiskInstBuilder.src_a_imm,
    zisk_inst_builder.ZiskInstBuilder.src_b_imm,
    zisk_inst_builder.ZiskInstBuilder.op_zisk,
    zisk_ops.ZiskOp.op_type,
    zisk_ops.ZiskOp.code,
    zisk_ops.ZiskOp.input_size,
    zisk_ops.ZiskOp.is_m32,
    zisk_inst.ZiskOperationType.Insts.CoreConvertFromOpType.from,
    zisk_inst_builder.ZiskInstBuilder.set_runtime_op_fields,
    zisk_inst_builder.ZiskInstBuilder.store_reg,
    zisk_inst_builder.ZiskInstBuilder.j,
    zisk_inst_builder.ZiskInstBuilder.build,
    riscv2zisk_context.Riscv2ZiskContext.insert_inst,
    zisk_registers.REGS_IN_MAIN_FROM,
    zisk_registers.REGS_IN_MAIN_TO,
    zisk_registers.REG_FIRST,
    mem.SYS_ADDR,
    mem.RAM_ADDR,
    UScalar.cast,
    UScalar.hcast,
    IScalar.hcast,
    lift,
    one_u64_scalar_ne_zero,
    one_i64_scalar_ne_zero,
    one_u64_val_not_lt_regs_from_set_width,
    regs_to_set_width_val_not_lt_one_u64,
    one_i64_val_not_lt_regs_from_set_width,
    regs_to_set_width_val_not_lt_one_i64,
    uscalar64_shift_right_i32_32_ok_true]

/-- Production ADDI wrapper milestone. The `addi` lowering path calls
`immediate_op_or_x0_copyb_typed`, not just the plain immediate helper. With
ordinary register routing fixed, this keeps the immediate symbolic while
checking the production wrapper branch where `rs1 != x0`. -/
theorem empty_addi_wrapper_reg1_materializes_result
    (imm : Std.I32) :
    helperMaterializesResult
      (fun ctx =>
        riscv2zisk_context.Riscv2ZiskContext.immediate_op_or_x0_copyb_typed
          ctx
          { rom_address := 0#u64, rd := 1#u32, rs1 := 1#u32,
            rs2 := 0#u32, imm := imm }
          zisk_ops.ZiskOp.Add 4#u64) = ok true := by
  simp [helperMaterializesResult, emptyExtractContext,
    riscv2zisk_context.Riscv2ZiskContext.immediate_op_or_x0_copyb_typed,
    zisk_inst_builder.ZiskInstBuilder.new_for_rv64im_lowering,
    zisk_inst_builder.ZiskInstBuilder.new,
    zisk_inst_builder.ZiskInstBuilder.Insts.CoreDefaultDefault.default,
    zisk_inst.ZiskInst.Insts.CoreDefaultDefault.default,
    zisk_inst_builder.ZiskInstBuilder.src_a_reg,
    zisk_inst_builder.ZiskInstBuilder.src_a_imm,
    zisk_inst_builder.ZiskInstBuilder.src_b_imm,
    zisk_inst_builder.ZiskInstBuilder.op_zisk,
    zisk_ops.ZiskOp.op_type,
    zisk_ops.ZiskOp.code,
    zisk_ops.ZiskOp.input_size,
    zisk_ops.ZiskOp.is_m32,
    zisk_inst.ZiskOperationType.Insts.CoreConvertFromOpType.from,
    zisk_inst_builder.ZiskInstBuilder.set_runtime_op_fields,
    zisk_inst_builder.ZiskInstBuilder.store_reg,
    zisk_inst_builder.ZiskInstBuilder.j,
    zisk_inst_builder.ZiskInstBuilder.build,
    riscv2zisk_context.Riscv2ZiskContext.insert_inst,
    zisk_registers.REGS_IN_MAIN_FROM,
    zisk_registers.REGS_IN_MAIN_TO,
    zisk_registers.REG_FIRST,
    mem.SYS_ADDR,
    mem.RAM_ADDR,
    UScalar.cast,
    UScalar.hcast,
    IScalar.hcast,
    lift,
    one_u64_scalar_ne_zero,
    one_i64_scalar_ne_zero,
    one_u64_val_not_lt_regs_from_set_width,
    regs_to_set_width_val_not_lt_one_u64,
    one_i64_val_not_lt_regs_from_set_width,
    regs_to_set_width_val_not_lt_one_i64,
    uscalar64_shift_right_i32_32_ok_true]

/-- Production HINT helper milestone. This covers the ADDI-family branch where
the destination is x0 and the instruction is not lowered as a NOP. -/
theorem empty_hint_reg1_materializes_result
    (imm : Std.I32) :
    helperMaterializesResult
      (fun ctx =>
        riscv2zisk_context.Riscv2ZiskContext.hint
          ctx
          { rom_address := 0#u64, rd := 0#u32, rs1 := 1#u32,
            rs2 := 0#u32, imm := imm }
          4#u64) = ok true := by
  simp [helperMaterializesResult, emptyExtractContext,
    riscv2zisk_context.Riscv2ZiskContext.hint,
    zisk_inst_builder.ZiskInstBuilder.new_for_rv64im_lowering,
    zisk_inst_builder.ZiskInstBuilder.new,
    zisk_inst_builder.ZiskInstBuilder.Insts.CoreDefaultDefault.default,
    zisk_inst.ZiskInst.Insts.CoreDefaultDefault.default,
    zisk_inst_builder.ZiskInstBuilder.src_a_reg,
    zisk_inst_builder.ZiskInstBuilder.src_a_imm,
    zisk_inst_builder.ZiskInstBuilder.src_b_imm,
    zisk_inst_builder.ZiskInstBuilder.op_zisk,
    zisk_ops.ZiskOp.op_type,
    zisk_ops.ZiskOp.code,
    zisk_ops.ZiskOp.input_size,
    zisk_ops.ZiskOp.is_m32,
    zisk_inst.ZiskOperationType.Insts.CoreConvertFromOpType.from,
    zisk_inst_builder.ZiskInstBuilder.set_runtime_op_fields,
    zisk_inst_builder.ZiskInstBuilder.j,
    zisk_inst_builder.ZiskInstBuilder.build,
    riscv2zisk_context.Riscv2ZiskContext.insert_inst,
    zisk_registers.REGS_IN_MAIN_FROM,
    zisk_registers.REGS_IN_MAIN_TO,
    zisk_registers.REG_FIRST,
    mem.SYS_ADDR,
    mem.RAM_ADDR,
    UScalar.cast,
    UScalar.hcast,
    IScalar.hcast,
    lift,
    one_u64_scalar_ne_zero,
    one_u64_val_not_lt_regs_from_set_width,
    regs_to_set_width_val_not_lt_one_u64,
    uscalar64_shift_right_i32_32_ok_true]

/-- Production R-type helper milestone for ordinary register routing. This
covers the shared helper used by the register-register arithmetic/logical
opcode surface. -/
theorem empty_register_add_reg1_materializes_result :
    helperMaterializesResult
      (fun ctx =>
        riscv2zisk_context.Riscv2ZiskContext.create_register_op_typed
          ctx
          { rom_address := 0#u64, rd := 1#u32, rs1 := 1#u32,
            rs2 := 1#u32, imm := 0#i32 }
          zisk_ops.ZiskOp.Add 4#u64) = ok true := by
  simp [helperMaterializesResult, emptyExtractContext,
    riscv2zisk_context.Riscv2ZiskContext.create_register_op_typed,
    zisk_inst_builder.ZiskInstBuilder.new_for_rv64im_lowering,
    zisk_inst_builder.ZiskInstBuilder.new,
    zisk_inst_builder.ZiskInstBuilder.Insts.CoreDefaultDefault.default,
    zisk_inst.ZiskInst.Insts.CoreDefaultDefault.default,
    zisk_inst_builder.ZiskInstBuilder.src_a_reg,
    zisk_inst_builder.ZiskInstBuilder.src_b_reg,
    zisk_inst_builder.ZiskInstBuilder.op_zisk,
    zisk_ops.ZiskOp.op_type,
    zisk_ops.ZiskOp.code,
    zisk_ops.ZiskOp.input_size,
    zisk_ops.ZiskOp.is_m32,
    zisk_inst.ZiskOperationType.Insts.CoreConvertFromOpType.from,
    zisk_inst_builder.ZiskInstBuilder.set_runtime_op_fields,
    zisk_inst_builder.ZiskInstBuilder.store_reg,
    zisk_inst_builder.ZiskInstBuilder.j,
    zisk_inst_builder.ZiskInstBuilder.build,
    riscv2zisk_context.Riscv2ZiskContext.insert_inst,
    zisk_registers.REGS_IN_MAIN_FROM,
    zisk_registers.REGS_IN_MAIN_TO,
    zisk_registers.REG_FIRST,
    mem.SYS_ADDR,
    mem.RAM_ADDR,
    UScalar.cast,
    UScalar.hcast,
    lift,
    one_u64_scalar_ne_zero,
    one_i64_scalar_ne_zero,
    one_u64_val_not_lt_regs_from_set_width,
    regs_to_set_width_val_not_lt_one_u64,
    one_i64_val_not_lt_regs_from_set_width,
    regs_to_set_width_val_not_lt_one_i64]

/-- Production branch helper milestone for ordinary register routing, with a
symbolic decoded branch offset. `neg = false` covers the fall-through/jump
ordering used by equality-style branch lowering. -/
theorem empty_branch_eq_reg1_materializes_result
    (imm : Std.I32) :
    helperMaterializesResult
      (fun ctx =>
        riscv2zisk_context.Riscv2ZiskContext.create_branch_op_typed
          ctx
          { rom_address := 0#u64, rd := 0#u32, rs1 := 1#u32,
            rs2 := 1#u32, imm := imm }
          zisk_ops.ZiskOp.Eq false 4#u64) = ok true := by
  simp [helperMaterializesResult, emptyExtractContext,
    riscv2zisk_context.Riscv2ZiskContext.create_branch_op_typed,
    zisk_inst_builder.ZiskInstBuilder.new_for_rv64im_lowering,
    zisk_inst_builder.ZiskInstBuilder.new,
    zisk_inst_builder.ZiskInstBuilder.Insts.CoreDefaultDefault.default,
    zisk_inst.ZiskInst.Insts.CoreDefaultDefault.default,
    zisk_inst_builder.ZiskInstBuilder.src_a_reg,
    zisk_inst_builder.ZiskInstBuilder.src_b_reg,
    zisk_inst_builder.ZiskInstBuilder.op_zisk,
    zisk_ops.ZiskOp.op_type,
    zisk_ops.ZiskOp.code,
    zisk_ops.ZiskOp.input_size,
    zisk_ops.ZiskOp.is_m32,
    zisk_inst.ZiskOperationType.Insts.CoreConvertFromOpType.from,
    zisk_inst_builder.ZiskInstBuilder.set_runtime_op_fields,
    zisk_inst_builder.ZiskInstBuilder.j,
    zisk_inst_builder.ZiskInstBuilder.build,
    riscv2zisk_context.Riscv2ZiskContext.insert_inst,
    zisk_registers.REGS_IN_MAIN_FROM,
    zisk_registers.REGS_IN_MAIN_TO,
    zisk_registers.REG_FIRST,
    mem.SYS_ADDR,
    mem.RAM_ADDR,
    UScalar.cast,
    UScalar.hcast,
    IScalar.cast,
    lift,
    one_u64_scalar_ne_zero,
    one_u64_val_not_lt_regs_from_set_width,
    regs_to_set_width_val_not_lt_one_u64]

/-- Production branch helper milestone for the alternate jump ordering used
when the branch condition is negated. -/
theorem empty_branch_ne_reg1_materializes_result
    (imm : Std.I32) :
    helperMaterializesResult
      (fun ctx =>
        riscv2zisk_context.Riscv2ZiskContext.create_branch_op_typed
          ctx
          { rom_address := 0#u64, rd := 0#u32, rs1 := 1#u32,
            rs2 := 1#u32, imm := imm }
          zisk_ops.ZiskOp.Eq true 4#u64) = ok true := by
  simp [helperMaterializesResult, emptyExtractContext,
    riscv2zisk_context.Riscv2ZiskContext.create_branch_op_typed,
    zisk_inst_builder.ZiskInstBuilder.new_for_rv64im_lowering,
    zisk_inst_builder.ZiskInstBuilder.new,
    zisk_inst_builder.ZiskInstBuilder.Insts.CoreDefaultDefault.default,
    zisk_inst.ZiskInst.Insts.CoreDefaultDefault.default,
    zisk_inst_builder.ZiskInstBuilder.src_a_reg,
    zisk_inst_builder.ZiskInstBuilder.src_b_reg,
    zisk_inst_builder.ZiskInstBuilder.op_zisk,
    zisk_ops.ZiskOp.op_type,
    zisk_ops.ZiskOp.code,
    zisk_ops.ZiskOp.input_size,
    zisk_ops.ZiskOp.is_m32,
    zisk_inst.ZiskOperationType.Insts.CoreConvertFromOpType.from,
    zisk_inst_builder.ZiskInstBuilder.set_runtime_op_fields,
    zisk_inst_builder.ZiskInstBuilder.j,
    zisk_inst_builder.ZiskInstBuilder.build,
    riscv2zisk_context.Riscv2ZiskContext.insert_inst,
    zisk_registers.REGS_IN_MAIN_FROM,
    zisk_registers.REGS_IN_MAIN_TO,
    zisk_registers.REG_FIRST,
    mem.SYS_ADDR,
    mem.RAM_ADDR,
    UScalar.cast,
    UScalar.hcast,
    IScalar.cast,
    lift,
    one_u64_scalar_ne_zero,
    one_u64_val_not_lt_regs_from_set_width,
    regs_to_set_width_val_not_lt_one_u64]

/-- Production copy helper milestone for fast paths copying rs1 into rd. -/
theorem empty_copyb_rs1_reg1_materializes_result :
    helperMaterializesResult
      (fun ctx =>
        riscv2zisk_context.Riscv2ZiskContext.copyb
          ctx
          { rom_address := 0#u64, rd := 1#u32, rs1 := 1#u32,
            rs2 := 1#u32, imm := 0#i32 }
          4#u64 1#u64) = ok true := by
  simp [helperMaterializesResult, emptyExtractContext,
    riscv2zisk_context.Riscv2ZiskContext.copyb,
    zisk_inst_builder.ZiskInstBuilder.new_for_rv64im_lowering,
    zisk_inst_builder.ZiskInstBuilder.new,
    zisk_inst_builder.ZiskInstBuilder.Insts.CoreDefaultDefault.default,
    zisk_inst.ZiskInst.Insts.CoreDefaultDefault.default,
    zisk_inst_builder.ZiskInstBuilder.src_a_imm,
    zisk_inst_builder.ZiskInstBuilder.src_b_reg,
    zisk_inst_builder.ZiskInstBuilder.op_zisk,
    zisk_ops.ZiskOp.op_type,
    zisk_ops.ZiskOp.code,
    zisk_ops.ZiskOp.input_size,
    zisk_ops.ZiskOp.is_m32,
    zisk_inst.ZiskOperationType.Insts.CoreConvertFromOpType.from,
    zisk_inst_builder.ZiskInstBuilder.set_runtime_op_fields,
    zisk_inst_builder.ZiskInstBuilder.store_reg,
    zisk_inst_builder.ZiskInstBuilder.j,
    zisk_inst_builder.ZiskInstBuilder.build,
    riscv2zisk_context.Riscv2ZiskContext.insert_inst,
    zisk_registers.REGS_IN_MAIN_FROM,
    zisk_registers.REGS_IN_MAIN_TO,
    zisk_registers.REG_FIRST,
    mem.SYS_ADDR,
    mem.RAM_ADDR,
    UScalar.cast,
    UScalar.hcast,
    lift,
    one_u64_scalar_ne_zero,
    one_i64_scalar_ne_zero,
    one_u64_val_not_lt_regs_from_set_width,
    regs_to_set_width_val_not_lt_one_u64,
    one_i64_val_not_lt_regs_from_set_width,
    regs_to_set_width_val_not_lt_one_i64,
    uscalar64_shift_right_i32_32_ok_true]

/-- Production copy helper milestone for fast paths copying rs2 into rd. -/
theorem empty_copyb_rs2_reg1_materializes_result :
    helperMaterializesResult
      (fun ctx =>
        riscv2zisk_context.Riscv2ZiskContext.copyb
          ctx
          { rom_address := 0#u64, rd := 1#u32, rs1 := 1#u32,
            rs2 := 1#u32, imm := 0#i32 }
          4#u64 2#u64) = ok true := by
  simp [helperMaterializesResult, emptyExtractContext,
    riscv2zisk_context.Riscv2ZiskContext.copyb,
    zisk_inst_builder.ZiskInstBuilder.new_for_rv64im_lowering,
    zisk_inst_builder.ZiskInstBuilder.new,
    zisk_inst_builder.ZiskInstBuilder.Insts.CoreDefaultDefault.default,
    zisk_inst.ZiskInst.Insts.CoreDefaultDefault.default,
    zisk_inst_builder.ZiskInstBuilder.src_a_imm,
    zisk_inst_builder.ZiskInstBuilder.src_b_reg,
    zisk_inst_builder.ZiskInstBuilder.op_zisk,
    zisk_ops.ZiskOp.op_type,
    zisk_ops.ZiskOp.code,
    zisk_ops.ZiskOp.input_size,
    zisk_ops.ZiskOp.is_m32,
    zisk_inst.ZiskOperationType.Insts.CoreConvertFromOpType.from,
    zisk_inst_builder.ZiskInstBuilder.set_runtime_op_fields,
    zisk_inst_builder.ZiskInstBuilder.store_reg,
    zisk_inst_builder.ZiskInstBuilder.j,
    zisk_inst_builder.ZiskInstBuilder.build,
    riscv2zisk_context.Riscv2ZiskContext.insert_inst,
    zisk_registers.REGS_IN_MAIN_FROM,
    zisk_registers.REGS_IN_MAIN_TO,
    zisk_registers.REG_FIRST,
    mem.SYS_ADDR,
    mem.RAM_ADDR,
    UScalar.cast,
    UScalar.hcast,
    lift,
    one_u64_scalar_ne_zero,
    one_i64_scalar_ne_zero,
    one_u64_val_not_lt_regs_from_set_width,
    regs_to_set_width_val_not_lt_one_u64,
    one_i64_val_not_lt_regs_from_set_width,
    regs_to_set_width_val_not_lt_one_i64,
    uscalar64_shift_right_i32_32_ok_true]

/-- Production LUI helper milestone with symbolic U-immediate payload. -/
theorem empty_lui_reg1_materializes_result
    (imm : Std.I32) :
    helperMaterializesResult
      (fun ctx =>
        riscv2zisk_context.Riscv2ZiskContext.lui
          ctx
          { rom_address := 0#u64, rd := 1#u32, rs1 := 0#u32,
            rs2 := 0#u32, imm := imm }
          4#u64) = ok true := by
  simp [helperMaterializesResult, emptyExtractContext,
    riscv2zisk_context.Riscv2ZiskContext.lui,
    zisk_inst_builder.ZiskInstBuilder.new_for_rv64im_lowering,
    zisk_inst_builder.ZiskInstBuilder.new,
    zisk_inst_builder.ZiskInstBuilder.Insts.CoreDefaultDefault.default,
    zisk_inst.ZiskInst.Insts.CoreDefaultDefault.default,
    zisk_inst_builder.ZiskInstBuilder.src_a_imm,
    zisk_inst_builder.ZiskInstBuilder.src_b_imm,
    zisk_inst_builder.ZiskInstBuilder.op_zisk,
    zisk_ops.ZiskOp.op_type,
    zisk_ops.ZiskOp.code,
    zisk_ops.ZiskOp.input_size,
    zisk_ops.ZiskOp.is_m32,
    zisk_inst.ZiskOperationType.Insts.CoreConvertFromOpType.from,
    zisk_inst_builder.ZiskInstBuilder.set_runtime_op_fields,
    zisk_inst_builder.ZiskInstBuilder.store_reg,
    zisk_inst_builder.ZiskInstBuilder.j,
    zisk_inst_builder.ZiskInstBuilder.build,
    riscv2zisk_context.Riscv2ZiskContext.insert_inst,
    zisk_registers.REGS_IN_MAIN_FROM,
    zisk_registers.REGS_IN_MAIN_TO,
    zisk_registers.REG_FIRST,
    mem.SYS_ADDR,
    mem.RAM_ADDR,
    UScalar.hcast,
    IScalar.hcast,
    lift,
    one_i64_scalar_ne_zero,
    one_i64_val_not_lt_regs_from_set_width,
    regs_to_set_width_val_not_lt_one_i64,
    uscalar64_shift_right_i32_32_ok_true]

/-- Production AUIPC helper milestone with symbolic U-immediate payload. -/
theorem empty_auipc_reg1_materializes_result
    (imm : Std.I32) :
    helperMaterializesResult
      (fun ctx =>
        riscv2zisk_context.Riscv2ZiskContext.auipc
          ctx
          { rom_address := 0#u64, rd := 1#u32, rs1 := 0#u32,
            rs2 := 0#u32, imm := imm }) = ok true := by
  simp [helperMaterializesResult, emptyExtractContext,
    riscv2zisk_context.Riscv2ZiskContext.auipc,
    zisk_inst_builder.ZiskInstBuilder.new_for_rv64im_lowering,
    zisk_inst_builder.ZiskInstBuilder.new,
    zisk_inst_builder.ZiskInstBuilder.Insts.CoreDefaultDefault.default,
    zisk_inst.ZiskInst.Insts.CoreDefaultDefault.default,
    zisk_inst_builder.ZiskInstBuilder.src_a_imm,
    zisk_inst_builder.ZiskInstBuilder.src_b_imm,
    zisk_inst_builder.ZiskInstBuilder.op_zisk,
    zisk_ops.ZiskOp.op_type,
    zisk_ops.ZiskOp.code,
    zisk_ops.ZiskOp.input_size,
    zisk_ops.ZiskOp.is_m32,
    zisk_inst.ZiskOperationType.Insts.CoreConvertFromOpType.from,
    zisk_inst_builder.ZiskInstBuilder.set_runtime_op_fields,
    zisk_inst_builder.ZiskInstBuilder.store_pc_reg,
    zisk_inst_builder.ZiskInstBuilder.store_reg,
    zisk_inst_builder.ZiskInstBuilder.j,
    zisk_inst_builder.ZiskInstBuilder.build,
    riscv2zisk_context.Riscv2ZiskContext.insert_inst,
    zisk_registers.REGS_IN_MAIN_FROM,
    zisk_registers.REGS_IN_MAIN_TO,
    zisk_registers.REG_FIRST,
    mem.SYS_ADDR,
    mem.RAM_ADDR,
    UScalar.hcast,
    IScalar.cast,
    lift,
    one_i64_scalar_ne_zero,
    one_i64_val_not_lt_regs_from_set_width,
    regs_to_set_width_val_not_lt_one_i64,
    uscalar64_shift_right_i32_32_ok_true]

/-- Production JAL helper milestone with symbolic J-immediate payload. -/
theorem empty_jal_reg1_materializes_result
    (imm : Std.I32) :
    helperMaterializesResult
      (fun ctx =>
        riscv2zisk_context.Riscv2ZiskContext.jal
          ctx
          { rom_address := 0#u64, rd := 1#u32, rs1 := 0#u32,
            rs2 := 0#u32, imm := imm }
          4#u64) = ok true := by
  simp [helperMaterializesResult, emptyExtractContext,
    riscv2zisk_context.Riscv2ZiskContext.jal,
    zisk_inst_builder.ZiskInstBuilder.new_for_rv64im_lowering,
    zisk_inst_builder.ZiskInstBuilder.new,
    zisk_inst_builder.ZiskInstBuilder.Insts.CoreDefaultDefault.default,
    zisk_inst.ZiskInst.Insts.CoreDefaultDefault.default,
    zisk_inst_builder.ZiskInstBuilder.src_a_imm,
    zisk_inst_builder.ZiskInstBuilder.src_b_imm,
    zisk_inst_builder.ZiskInstBuilder.op_zisk,
    zisk_ops.ZiskOp.op_type,
    zisk_ops.ZiskOp.code,
    zisk_ops.ZiskOp.input_size,
    zisk_ops.ZiskOp.is_m32,
    zisk_inst.ZiskOperationType.Insts.CoreConvertFromOpType.from,
    zisk_inst_builder.ZiskInstBuilder.set_runtime_op_fields,
    zisk_inst_builder.ZiskInstBuilder.store_pc_reg,
    zisk_inst_builder.ZiskInstBuilder.store_reg,
    zisk_inst_builder.ZiskInstBuilder.j,
    zisk_inst_builder.ZiskInstBuilder.build,
    riscv2zisk_context.Riscv2ZiskContext.insert_inst,
    zisk_registers.REGS_IN_MAIN_FROM,
    zisk_registers.REGS_IN_MAIN_TO,
    zisk_registers.REG_FIRST,
    mem.SYS_ADDR,
    mem.RAM_ADDR,
    UScalar.hcast,
    IScalar.cast,
    lift,
    one_i64_scalar_ne_zero,
    one_i64_val_not_lt_regs_from_set_width,
    regs_to_set_width_val_not_lt_one_i64,
    uscalar64_shift_right_i32_32_ok_true]

/-- Production JALR aligned branch milestone. This evaluates the extracted
production helper for an ordinary-register representative whose decoded
immediate satisfies `imm % 4 = 0`. It is Boolean-shaped because Aeneas
`Result` does not provide a convenient decidable equality for `native_decide`;
the predicate still runs through `helperMaterializesResult`. -/
theorem empty_jalr_aligned_reg1_materializes_result_flag :
    helperMaterializesResultFlag
      (fun ctx =>
        riscv2zisk_context.Riscv2ZiskContext.jalr
          ctx
          { rom_address := 0#u64, rd := 1#u32, rs1 := 1#u32,
            rs2 := 0#u32, imm := 0#i32 }
          4#u64) = true := by
  native_decide

/-- Production JALR unaligned branch milestone. This covers the extracted
two-row path used when the decoded immediate does not satisfy `imm % 4 = 0`. -/
theorem empty_jalr_unaligned_reg1_materializes_result_flag :
    helperMaterializesResultFlag
      (fun ctx =>
        riscv2zisk_context.Riscv2ZiskContext.jalr
          ctx
          { rom_address := 0#u64, rd := 1#u32, rs1 := 1#u32,
            rs2 := 0#u32, imm := 1#i32 }
          4#u64) = true := by
  native_decide

/-- Extracted `ZiskInstBuilder.ind_width` accepts the four memory widths used
by RV64IM load/store helpers. These lemmas isolate the Aeneas scalar-pattern
normalization step needed before proving the full symbolic load/store helper
totality theorem. -/
theorem ind_width_1_flag
    (zib : zisk_inst_builder.ZiskInstBuilder) :
    (match zisk_inst_builder.ZiskInstBuilder.ind_width zib 1#u64 with
     | ok _ => true
     | _ => false) = true := by
  rw [u64_1_eq_pattern]
  simp [zisk_inst_builder.ZiskInstBuilder.ind_width]

theorem ind_width_2_flag
    (zib : zisk_inst_builder.ZiskInstBuilder) :
    (match zisk_inst_builder.ZiskInstBuilder.ind_width zib 2#u64 with
     | ok _ => true
     | _ => false) = true := by
  rw [u64_2_eq_pattern]
  simp [zisk_inst_builder.ZiskInstBuilder.ind_width]

theorem ind_width_4_flag
    (zib : zisk_inst_builder.ZiskInstBuilder) :
    (match zisk_inst_builder.ZiskInstBuilder.ind_width zib 4#u64 with
     | ok _ => true
     | _ => false) = true := by
  rw [u64_4_eq_pattern]
  simp [zisk_inst_builder.ZiskInstBuilder.ind_width]

theorem ind_width_8_flag
    (zib : zisk_inst_builder.ZiskInstBuilder) :
    (match zisk_inst_builder.ZiskInstBuilder.ind_width zib 8#u64 with
     | ok _ => true
     | _ => false) = true := by
  rw [u64_8_eq_pattern]
  simp [zisk_inst_builder.ZiskInstBuilder.ind_width]

/-- Ordinary register-routing milestones for the extracted builder helpers.
They isolate the register-bound comparisons that appear in most row-builder
paths before those paths can be lifted from representative checks to symbolic
helper-total theorems. -/
theorem src_a_reg_one_flag
    (zib : zisk_inst_builder.ZiskInstBuilder) :
    builderOkFlag
      (zisk_inst_builder.ZiskInstBuilder.src_a_reg zib 1#u64 false) = true := by
  simp [builderOkFlag,
    zisk_inst_builder.ZiskInstBuilder.src_a_reg,
    zisk_registers.REGS_IN_MAIN_FROM,
    zisk_registers.REGS_IN_MAIN_TO,
    zisk_registers.REG_FIRST,
    UScalar.cast,
    lift,
    one_nat_not_lt_regs_from_set_width,
    regs_to_set_width_nat_ne_zero]

theorem src_b_reg_one_flag
    (zib : zisk_inst_builder.ZiskInstBuilder) :
    builderOkFlag
      (zisk_inst_builder.ZiskInstBuilder.src_b_reg zib 1#u64 false) = true := by
  simp [builderOkFlag,
    zisk_inst_builder.ZiskInstBuilder.src_b_reg,
    zisk_registers.REGS_IN_MAIN_FROM,
    zisk_registers.REGS_IN_MAIN_TO,
    zisk_registers.REG_FIRST,
    UScalar.cast,
    lift,
    one_nat_not_lt_regs_from_set_width,
    regs_to_set_width_nat_ne_zero]

theorem src_a_reg_two_flag
    (zib : zisk_inst_builder.ZiskInstBuilder) :
    builderOkFlag
      (zisk_inst_builder.ZiskInstBuilder.src_a_reg zib 2#u64 false) = true := by
  simp [builderOkFlag,
    zisk_inst_builder.ZiskInstBuilder.src_a_reg,
    zisk_registers.REGS_IN_MAIN_FROM,
    zisk_registers.REGS_IN_MAIN_TO,
    zisk_registers.REG_FIRST,
    UScalar.cast,
    lift,
    two_nat_not_lt_regs_from_set_width,
    regs_to_set_width_nat_not_le_one]

theorem src_b_reg_two_flag
    (zib : zisk_inst_builder.ZiskInstBuilder) :
    builderOkFlag
      (zisk_inst_builder.ZiskInstBuilder.src_b_reg zib 2#u64 false) = true := by
  simp [builderOkFlag,
    zisk_inst_builder.ZiskInstBuilder.src_b_reg,
    zisk_registers.REGS_IN_MAIN_FROM,
    zisk_registers.REGS_IN_MAIN_TO,
    zisk_registers.REG_FIRST,
    UScalar.cast,
    lift,
    two_nat_not_lt_regs_from_set_width,
    regs_to_set_width_nat_not_le_one]

theorem store_reg_one_flag
    (zib : zisk_inst_builder.ZiskInstBuilder) :
    builderOkFlag
      (zisk_inst_builder.ZiskInstBuilder.store_reg zib 1#i64 false false) = true := by
  simp [builderOkFlag,
    zisk_inst_builder.ZiskInstBuilder.store_reg,
    zisk_registers.REGS_IN_MAIN_FROM,
    zisk_registers.REGS_IN_MAIN_TO,
    zisk_registers.REG_FIRST,
    UScalar.hcast,
    lift,
    one_int_not_lt_regs_from_set_width,
    regs_to_set_width_int_not_lt_one]

theorem store_reg_two_flag
    (zib : zisk_inst_builder.ZiskInstBuilder) :
    builderOkFlag
      (zisk_inst_builder.ZiskInstBuilder.store_reg zib 2#i64 false false) = true := by
  simp [builderOkFlag,
    zisk_inst_builder.ZiskInstBuilder.store_reg,
    zisk_registers.REGS_IN_MAIN_FROM,
    zisk_registers.REGS_IN_MAIN_TO,
    zisk_registers.REG_FIRST,
    UScalar.hcast,
    lift,
    two_int_not_lt_regs_from_set_width,
    regs_to_set_width_int_not_lt_two]

theorem src_a_reg_all_rv_regs_flag
    (zib : zisk_inst_builder.ZiskInstBuilder) :
    allRvU64Regs.all
      (fun reg =>
        builderOkFlag
          (zisk_inst_builder.ZiskInstBuilder.src_a_reg zib reg false)) = true := by
  simp [allRvU64Regs,
    zisk_inst_builder.ZiskInstBuilder.src_a_reg,
    zisk_registers.REGS_IN_MAIN_FROM,
    zisk_registers.REGS_IN_MAIN_TO,
    zisk_registers.REG_FIRST,
    UScalar.cast,
    lift,
    src_a_imm_zero_flag,
    regs_from_set_width_u64_val_eq,
    regs_to_set_width_u64_val_eq]
  simp [builderOkFlag]

theorem src_b_reg_all_rv_regs_flag
    (zib : zisk_inst_builder.ZiskInstBuilder) :
    allRvU64Regs.all
      (fun reg =>
        builderOkFlag
          (zisk_inst_builder.ZiskInstBuilder.src_b_reg zib reg false)) = true := by
  simp [allRvU64Regs,
    zisk_inst_builder.ZiskInstBuilder.src_b_reg,
    zisk_registers.REGS_IN_MAIN_FROM,
    zisk_registers.REGS_IN_MAIN_TO,
    zisk_registers.REG_FIRST,
    UScalar.cast,
    lift,
    src_b_imm_zero_flag,
    regs_from_set_width_u64_val_eq,
    regs_to_set_width_u64_val_eq]
  simp [builderOkFlag]

theorem store_reg_all_rv_regs_flag
    (zib : zisk_inst_builder.ZiskInstBuilder) :
    allRvI64Regs.all
      (fun reg =>
        builderOkFlag
          (zisk_inst_builder.ZiskInstBuilder.store_reg zib reg false false)) = true := by
  simp [allRvI64Regs,
    zisk_inst_builder.ZiskInstBuilder.store_reg,
    zisk_registers.REGS_IN_MAIN_FROM,
    zisk_registers.REGS_IN_MAIN_TO,
    zisk_registers.REG_FIRST,
    UScalar.hcast,
    lift,
    regs_from_set_width_i64_val_eq,
    regs_to_set_width_i64_val_eq]
  simp [builderOkFlag]

theorem u64_one_add_zero_ok :
    ((1#64#uscalar : Std.U64) + 0#u64) = ok (1#64#uscalar : Std.U64) := by
  rw [show ((1#64#uscalar : Std.U64) + 0#u64) =
      UScalar.add (1#64#uscalar : Std.U64) 0#u64 by rfl]
  unfold UScalar.add UScalar.tryMk Result.ofOption UScalar.tryMkOpt
  simp
  apply congrArg Result.ok
  apply UScalar.eq_of_val_eq
  native_decide

theorem i64_one_add_zero_ok :
    ((1#64#iscalar : Std.I64) + 0#i64) = ok (1#64#iscalar : Std.I64) := by
  rw [show ((1#64#iscalar : Std.I64) + 0#i64) =
      IScalar.add (1#64#iscalar : Std.I64) 0#i64 by rfl]
  unfold IScalar.add IScalar.tryMk Result.ofOption IScalar.tryMkOpt
  simp
  apply congrArg Result.ok
  apply IScalar.eq_of_val_eq
  native_decide

theorem i64_zero_val : (0#i64 : Std.I64).val = 0 := by
  native_decide

theorem u64_zero_val : (0#u64 : Std.U64).val = 0 := by
  native_decide

theorem i64_add_zero_ok (x : Std.I64) :
    x + 0#i64 = ok x := by
  have h := IScalar.add_equiv x (0#i64 : Std.I64)
  cases h_add : x + 0#i64 <;> rw [h_add] at h
  · rcases h with ⟨_h_bounds, h_val, _h_bv⟩
    apply congrArg Result.ok
    apply IScalar.eq_of_val_eq
    simpa [i64_zero_val] using h_val
  · exfalso
    apply h
    simpa [IScalar.inBounds, i64_zero_val] using x.hBounds
  · exact False.elim h

theorem u64_add_zero_ok (x : Std.U64) :
    x + 0#u64 = ok x := by
  have h := UScalar.add_equiv x (0#u64 : Std.U64)
  cases h_add : x + 0#u64 <;> rw [h_add] at h
  · rcases h with ⟨_h_bounds, h_val, _h_bv⟩
    apply congrArg Result.ok
    apply UScalar.eq_of_val_eq
    simpa [u64_zero_val] using h_val
  · exfalso
    apply h
    simpa [UScalar.inBounds, u64_zero_val] using x.hBounds
  · exact False.elim h

theorem u64_zero_shift_right_32_ok :
    ((0#u64 : Std.U64) >>> (32#i32 : Std.I32)) = ok (0#u64 : Std.U64) := by
  rw [show ((0#u64 : Std.U64) >>> (32#i32 : Std.I32)) =
      UScalar.shiftRight_IScalar (0#u64 : Std.U64) (32#i32 : Std.I32) by rfl]
  unfold UScalar.shiftRight_IScalar UScalar.shiftRight
  simp
  exact u64_zero_eq_zero

theorem u64_mk_ofNat_val (n : Nat) :
    (↑(Aeneas.Std.UScalar.mk (BitVec.ofNat 64 n) : Std.U64) : Nat) = n % 2 ^ 64 := by
  simp [UScalar.val]

theorem i64_mk_ofNat_val (n : Nat) :
    (↑(Aeneas.Std.IScalar.mk (BitVec.ofNat 64 n) : Std.I64) : Int) =
      (BitVec.ofNat 64 n).toInt := by
  simp [IScalar.val]

/-- Production load-helper materialization milestones for each indirect memory
width used by RV64IM load opcodes. These are representative ordinary-register
checks over the extracted production helper; signedness-specific behavior is
handled by the opcode/circuit equivalence layer, while this proves the shared
load row-builder path emits a row for each width. -/
theorem empty_load_width1_reg1_materializes_result_flag :
    helperMaterializesResultFlag
      (fun ctx =>
        riscv2zisk_context.Riscv2ZiskContext.load_op_typed
          ctx
          { rom_address := 0#u64, rd := 1#u32, rs1 := 1#u32,
            rs2 := 0#u32, imm := 0#i32 }
          zisk_ops.ZiskOp.Add 1#u64 4#u64) = true := by
  native_decide

theorem empty_load_width2_reg1_materializes_result_flag :
    helperMaterializesResultFlag
      (fun ctx =>
        riscv2zisk_context.Riscv2ZiskContext.load_op_typed
          ctx
          { rom_address := 0#u64, rd := 1#u32, rs1 := 1#u32,
            rs2 := 0#u32, imm := 0#i32 }
          zisk_ops.ZiskOp.Add 2#u64 4#u64) = true := by
  native_decide

theorem empty_load_width4_reg1_materializes_result_flag :
    helperMaterializesResultFlag
      (fun ctx =>
        riscv2zisk_context.Riscv2ZiskContext.load_op_typed
          ctx
          { rom_address := 0#u64, rd := 1#u32, rs1 := 1#u32,
            rs2 := 0#u32, imm := 0#i32 }
          zisk_ops.ZiskOp.Add 4#u64 4#u64) = true := by
  native_decide

theorem empty_load_width8_reg1_materializes_result_flag :
    helperMaterializesResultFlag
      (fun ctx =>
        riscv2zisk_context.Riscv2ZiskContext.load_op_typed
          ctx
          { rom_address := 0#u64, rd := 1#u32, rs1 := 1#u32,
            rs2 := 0#u32, imm := 0#i32 }
          zisk_ops.ZiskOp.Add 8#u64 4#u64) = true := by
  native_decide

/- Finite all-register load-helper materialization at zero immediate. These
cover every RV `rd × rs1` pair for each indirect memory width, complementing
the symbolic-immediate representative-register milestones below. -/
set_option maxHeartbeats 4000000 in
theorem all_load_width1_zero_imm_materializes_result_flag :
    allRvU32Regs.all
      (fun rd =>
        allRvU32Regs.all
          (fun rs1 =>
            helperMaterializesResultFlag
              (fun ctx =>
                riscv2zisk_context.Riscv2ZiskContext.load_op_typed
                  ctx
                  { rom_address := 0#u64, rd := rd, rs1 := rs1,
                    rs2 := 0#u32, imm := 0#i32 }
                  zisk_ops.ZiskOp.Add 1#u64 4#u64))) = true := by
  native_decide

set_option maxHeartbeats 4000000 in
theorem all_load_width2_zero_imm_materializes_result_flag :
    allRvU32Regs.all
      (fun rd =>
        allRvU32Regs.all
          (fun rs1 =>
            helperMaterializesResultFlag
              (fun ctx =>
                riscv2zisk_context.Riscv2ZiskContext.load_op_typed
                  ctx
                  { rom_address := 0#u64, rd := rd, rs1 := rs1,
                    rs2 := 0#u32, imm := 0#i32 }
                  zisk_ops.ZiskOp.Add 2#u64 4#u64))) = true := by
  native_decide

set_option maxHeartbeats 4000000 in
theorem all_load_width4_zero_imm_materializes_result_flag :
    allRvU32Regs.all
      (fun rd =>
        allRvU32Regs.all
          (fun rs1 =>
            helperMaterializesResultFlag
              (fun ctx =>
                riscv2zisk_context.Riscv2ZiskContext.load_op_typed
                  ctx
                  { rom_address := 0#u64, rd := rd, rs1 := rs1,
                    rs2 := 0#u32, imm := 0#i32 }
                  zisk_ops.ZiskOp.Add 4#u64 4#u64))) = true := by
  native_decide

set_option maxHeartbeats 4000000 in
theorem all_load_width8_zero_imm_materializes_result_flag :
    allRvU32Regs.all
      (fun rd =>
        allRvU32Regs.all
          (fun rs1 =>
            helperMaterializesResultFlag
              (fun ctx =>
                riscv2zisk_context.Riscv2ZiskContext.load_op_typed
                  ctx
                  { rom_address := 0#u64, rd := rd, rs1 := rs1,
                    rs2 := 0#u32, imm := 0#i32 }
                  zisk_ops.ZiskOp.Add 8#u64 4#u64))) = true := by
  native_decide

/- The symbolic-immediate load-helper materialization edge grid keeps `imm`
universally quantified while covering zero, ordinary, and upper-edge registers. -/
set_option maxHeartbeats 2000000 in
theorem edge_load_width1_symbolic_imm_materializes_result_flag
    (imm : Std.I32) :
    edgeRvU32Regs.all
      (fun rd =>
        edgeRvU32Regs.all
          (fun rs1 =>
            helperMaterializesResultFlag
              (fun ctx =>
                riscv2zisk_context.Riscv2ZiskContext.load_op_typed
                  ctx
                  { rom_address := 0#u64, rd := rd, rs1 := rs1,
                    rs2 := 0#u32, imm := imm }
                  zisk_ops.ZiskOp.Add 1#u64 4#u64))) = true := by
  rw [u64_1_eq_pattern]
  simp [edgeRvU32Regs, helperMaterializesResultFlag, helperMaterializesResult,
    emptyExtractContext,
    riscv2zisk_context.Riscv2ZiskContext.load_op_typed,
    riscv2zisk_context.Riscv2ZiskContext.load_op_with_reg_offset,
    zisk_inst_builder.ZiskInstBuilder.new_for_rv64im_lowering,
    zisk_inst_builder.ZiskInstBuilder.new,
    zisk_inst_builder.ZiskInstBuilder.Insts.CoreDefaultDefault.default,
    zisk_inst.ZiskInst.Insts.CoreDefaultDefault.default,
    zisk_inst_builder.ZiskInstBuilder.src_a_imm,
    zisk_inst_builder.ZiskInstBuilder.src_a_reg,
    zisk_inst_builder.ZiskInstBuilder.ind_width,
    zisk_inst_builder.ZiskInstBuilder.src_b_ind,
    zisk_inst_builder.ZiskInstBuilder.op_zisk,
    zisk_ops.ZiskOp.op_type,
    zisk_ops.ZiskOp.code,
    zisk_ops.ZiskOp.input_size,
    zisk_ops.ZiskOp.is_m32,
    zisk_inst.ZiskOperationType.Insts.CoreConvertFromOpType.from,
    zisk_inst_builder.ZiskInstBuilder.set_runtime_op_fields,
    zisk_inst_builder.ZiskInstBuilder.store_reg,
    zisk_inst_builder.ZiskInstBuilder.j,
    zisk_inst_builder.ZiskInstBuilder.build,
    riscv2zisk_context.Riscv2ZiskContext.insert_inst,
    zisk_registers.REGS_IN_MAIN_FROM,
    zisk_registers.REGS_IN_MAIN_TO,
    zisk_registers.REG_FIRST,
    mem.SYS_ADDR,
    mem.RAM_ADDR,
    UScalar.cast,
    UScalar.hcast,
    IScalar.cast,
    IScalar.hcast,
    UScalar.add,
    IScalar.add,
    UScalar.tryMk,
    IScalar.tryMk,
    UScalar.tryMkOpt,
    IScalar.tryMkOpt,
    Result.ofOption,
    lift,
    regs_from_set_width_u64_val_eq,
    regs_to_set_width_u64_val_eq,
    regs_from_set_width_i64_val_eq,
    regs_to_set_width_i64_val_eq,
    u64_add_zero_ok,
    i64_add_zero_ok,
    u64_zero_eq_zero,
    u64_zero_shift_right_32_ok,
    i64_zero_eq_zero,
    one_u64_scalar_ne_zero,
    one_i64_scalar_ne_zero,
    u64_one_val_ne_zero,
    u64_one_val_not_gt_regs_to,
    u64_31_ne_zero,
    u64_31_val_ne_zero,
    u64_31_val_not_gt_regs_to,
    i64_one_val_not_lt_regs_from,
    i64_one_val_not_gt_regs_to,
    i64_31_ne_zero,
    i64_31_val_not_lt_regs_from,
    i64_31_val_not_gt_regs_to,
    one_u64_val_not_lt_regs_from_set_width,
    regs_to_set_width_val_not_lt_one_u64,
    one_i64_val_not_lt_regs_from_set_width,
    regs_to_set_width_val_not_lt_one_i64]

set_option maxHeartbeats 2000000 in
theorem edge_load_width2_symbolic_imm_materializes_result_flag
    (imm : Std.I32) :
    edgeRvU32Regs.all
      (fun rd =>
        edgeRvU32Regs.all
          (fun rs1 =>
            helperMaterializesResultFlag
              (fun ctx =>
                riscv2zisk_context.Riscv2ZiskContext.load_op_typed
                  ctx
                  { rom_address := 0#u64, rd := rd, rs1 := rs1,
                    rs2 := 0#u32, imm := imm }
                  zisk_ops.ZiskOp.Add 2#u64 4#u64))) = true := by
  rw [u64_2_eq_pattern]
  simp [edgeRvU32Regs, helperMaterializesResultFlag, helperMaterializesResult,
    emptyExtractContext,
    riscv2zisk_context.Riscv2ZiskContext.load_op_typed,
    riscv2zisk_context.Riscv2ZiskContext.load_op_with_reg_offset,
    zisk_inst_builder.ZiskInstBuilder.new_for_rv64im_lowering,
    zisk_inst_builder.ZiskInstBuilder.new,
    zisk_inst_builder.ZiskInstBuilder.Insts.CoreDefaultDefault.default,
    zisk_inst.ZiskInst.Insts.CoreDefaultDefault.default,
    zisk_inst_builder.ZiskInstBuilder.src_a_imm,
    zisk_inst_builder.ZiskInstBuilder.src_a_reg,
    zisk_inst_builder.ZiskInstBuilder.ind_width,
    zisk_inst_builder.ZiskInstBuilder.src_b_ind,
    zisk_inst_builder.ZiskInstBuilder.op_zisk,
    zisk_ops.ZiskOp.op_type,
    zisk_ops.ZiskOp.code,
    zisk_ops.ZiskOp.input_size,
    zisk_ops.ZiskOp.is_m32,
    zisk_inst.ZiskOperationType.Insts.CoreConvertFromOpType.from,
    zisk_inst_builder.ZiskInstBuilder.set_runtime_op_fields,
    zisk_inst_builder.ZiskInstBuilder.store_reg,
    zisk_inst_builder.ZiskInstBuilder.j,
    zisk_inst_builder.ZiskInstBuilder.build,
    riscv2zisk_context.Riscv2ZiskContext.insert_inst,
    zisk_registers.REGS_IN_MAIN_FROM,
    zisk_registers.REGS_IN_MAIN_TO,
    zisk_registers.REG_FIRST,
    mem.SYS_ADDR,
    mem.RAM_ADDR,
    UScalar.cast,
    UScalar.hcast,
    IScalar.hcast,
    lift,
    regs_from_set_width_u64_val_eq,
    regs_to_set_width_u64_val_eq,
    regs_from_set_width_i64_val_eq,
    regs_to_set_width_i64_val_eq,
    i64_add_zero_ok,
    u64_zero_eq_zero,
    u64_zero_shift_right_32_ok,
    i64_zero_eq_zero,
    one_i64_scalar_ne_zero,
    u64_one_val_ne_zero,
    u64_one_val_not_gt_regs_to,
    u64_31_val_ne_zero,
    u64_31_val_not_gt_regs_to,
    i64_one_val_not_lt_regs_from,
    i64_one_val_not_gt_regs_to,
    i64_31_ne_zero,
    i64_31_val_not_lt_regs_from,
    i64_31_val_not_gt_regs_to,
    one_u64_val_not_lt_regs_from_set_width,
    regs_to_set_width_val_not_lt_one_u64,
    one_i64_val_not_lt_regs_from_set_width,
    regs_to_set_width_val_not_lt_one_i64]

set_option maxHeartbeats 2000000 in
theorem edge_load_width4_symbolic_imm_materializes_result_flag
    (imm : Std.I32) :
    edgeRvU32Regs.all
      (fun rd =>
        edgeRvU32Regs.all
          (fun rs1 =>
            helperMaterializesResultFlag
              (fun ctx =>
                riscv2zisk_context.Riscv2ZiskContext.load_op_typed
                  ctx
                  { rom_address := 0#u64, rd := rd, rs1 := rs1,
                    rs2 := 0#u32, imm := imm }
                  zisk_ops.ZiskOp.Add 4#u64 4#u64))) = true := by
  rw [u64_4_eq_pattern]
  simp [edgeRvU32Regs, helperMaterializesResultFlag, helperMaterializesResult,
    emptyExtractContext,
    riscv2zisk_context.Riscv2ZiskContext.load_op_typed,
    riscv2zisk_context.Riscv2ZiskContext.load_op_with_reg_offset,
    zisk_inst_builder.ZiskInstBuilder.new_for_rv64im_lowering,
    zisk_inst_builder.ZiskInstBuilder.new,
    zisk_inst_builder.ZiskInstBuilder.Insts.CoreDefaultDefault.default,
    zisk_inst.ZiskInst.Insts.CoreDefaultDefault.default,
    zisk_inst_builder.ZiskInstBuilder.src_a_imm,
    zisk_inst_builder.ZiskInstBuilder.src_a_reg,
    zisk_inst_builder.ZiskInstBuilder.ind_width,
    zisk_inst_builder.ZiskInstBuilder.src_b_ind,
    zisk_inst_builder.ZiskInstBuilder.op_zisk,
    zisk_ops.ZiskOp.op_type,
    zisk_ops.ZiskOp.code,
    zisk_ops.ZiskOp.input_size,
    zisk_ops.ZiskOp.is_m32,
    zisk_inst.ZiskOperationType.Insts.CoreConvertFromOpType.from,
    zisk_inst_builder.ZiskInstBuilder.set_runtime_op_fields,
    zisk_inst_builder.ZiskInstBuilder.store_reg,
    zisk_inst_builder.ZiskInstBuilder.j,
    zisk_inst_builder.ZiskInstBuilder.build,
    riscv2zisk_context.Riscv2ZiskContext.insert_inst,
    zisk_registers.REGS_IN_MAIN_FROM,
    zisk_registers.REGS_IN_MAIN_TO,
    zisk_registers.REG_FIRST,
    mem.SYS_ADDR,
    mem.RAM_ADDR,
    UScalar.cast,
    UScalar.hcast,
    IScalar.hcast,
    lift,
    regs_from_set_width_u64_val_eq,
    regs_to_set_width_u64_val_eq,
    regs_from_set_width_i64_val_eq,
    regs_to_set_width_i64_val_eq,
    i64_add_zero_ok,
    u64_zero_eq_zero,
    u64_zero_shift_right_32_ok,
    i64_zero_eq_zero,
    one_i64_scalar_ne_zero,
    u64_one_val_ne_zero,
    u64_one_val_not_gt_regs_to,
    u64_31_val_ne_zero,
    u64_31_val_not_gt_regs_to,
    i64_one_val_not_lt_regs_from,
    i64_one_val_not_gt_regs_to,
    i64_31_ne_zero,
    i64_31_val_not_lt_regs_from,
    i64_31_val_not_gt_regs_to,
    one_u64_val_not_lt_regs_from_set_width,
    regs_to_set_width_val_not_lt_one_u64,
    one_i64_val_not_lt_regs_from_set_width,
    regs_to_set_width_val_not_lt_one_i64]

set_option maxHeartbeats 2000000 in
theorem edge_load_width8_symbolic_imm_materializes_result_flag
    (imm : Std.I32) :
    edgeRvU32Regs.all
      (fun rd =>
        edgeRvU32Regs.all
          (fun rs1 =>
            helperMaterializesResultFlag
              (fun ctx =>
                riscv2zisk_context.Riscv2ZiskContext.load_op_typed
                  ctx
                  { rom_address := 0#u64, rd := rd, rs1 := rs1,
                    rs2 := 0#u32, imm := imm }
                  zisk_ops.ZiskOp.Add 8#u64 4#u64))) = true := by
  rw [u64_8_eq_pattern]
  simp [edgeRvU32Regs, helperMaterializesResultFlag, helperMaterializesResult,
    emptyExtractContext,
    riscv2zisk_context.Riscv2ZiskContext.load_op_typed,
    riscv2zisk_context.Riscv2ZiskContext.load_op_with_reg_offset,
    zisk_inst_builder.ZiskInstBuilder.new_for_rv64im_lowering,
    zisk_inst_builder.ZiskInstBuilder.new,
    zisk_inst_builder.ZiskInstBuilder.Insts.CoreDefaultDefault.default,
    zisk_inst.ZiskInst.Insts.CoreDefaultDefault.default,
    zisk_inst_builder.ZiskInstBuilder.src_a_imm,
    zisk_inst_builder.ZiskInstBuilder.src_a_reg,
    zisk_inst_builder.ZiskInstBuilder.ind_width,
    zisk_inst_builder.ZiskInstBuilder.src_b_ind,
    zisk_inst_builder.ZiskInstBuilder.op_zisk,
    zisk_ops.ZiskOp.op_type,
    zisk_ops.ZiskOp.code,
    zisk_ops.ZiskOp.input_size,
    zisk_ops.ZiskOp.is_m32,
    zisk_inst.ZiskOperationType.Insts.CoreConvertFromOpType.from,
    zisk_inst_builder.ZiskInstBuilder.set_runtime_op_fields,
    zisk_inst_builder.ZiskInstBuilder.store_reg,
    zisk_inst_builder.ZiskInstBuilder.j,
    zisk_inst_builder.ZiskInstBuilder.build,
    riscv2zisk_context.Riscv2ZiskContext.insert_inst,
    zisk_registers.REGS_IN_MAIN_FROM,
    zisk_registers.REGS_IN_MAIN_TO,
    zisk_registers.REG_FIRST,
    mem.SYS_ADDR,
    mem.RAM_ADDR,
    UScalar.cast,
    UScalar.hcast,
    IScalar.hcast,
    lift,
    regs_from_set_width_u64_val_eq,
    regs_to_set_width_u64_val_eq,
    regs_from_set_width_i64_val_eq,
    regs_to_set_width_i64_val_eq,
    i64_add_zero_ok,
    u64_zero_eq_zero,
    u64_zero_shift_right_32_ok,
    i64_zero_eq_zero,
    one_i64_scalar_ne_zero,
    u64_one_val_ne_zero,
    u64_one_val_not_gt_regs_to,
    u64_31_val_ne_zero,
    u64_31_val_not_gt_regs_to,
    i64_one_val_not_lt_regs_from,
    i64_one_val_not_gt_regs_to,
    i64_31_ne_zero,
    i64_31_val_not_lt_regs_from,
    i64_31_val_not_gt_regs_to,
    one_u64_val_not_lt_regs_from_set_width,
    regs_to_set_width_val_not_lt_one_u64,
    one_i64_val_not_lt_regs_from_set_width,
    regs_to_set_width_val_not_lt_one_i64]

/- Full `rd × rs1` symbolic-immediate grid for width-1 loads. This is the
same extracted production helper as the edge-grid checks, with scalar literal
branch decisions discharged by generic Aeneas scalar-value facts. -/
set_option maxHeartbeats 2000000 in
theorem all_load_width1_symbolic_imm_materializes_result_flag
    (imm : Std.I32) :
    allRvU32Regs.all
      (fun rd =>
        allRvU32Regs.all
          (fun rs1 =>
            helperMaterializesResultFlag
              (fun ctx =>
                riscv2zisk_context.Riscv2ZiskContext.load_op_typed
                  ctx
                  { rom_address := 0#u64, rd := rd, rs1 := rs1,
                    rs2 := 0#u32, imm := imm }
                  zisk_ops.ZiskOp.Add 1#u64 4#u64))) = true := by
  rw [u64_1_eq_pattern]
  simp [allRvU32Regs, helperMaterializesResultFlag, helperMaterializesResult,
    emptyExtractContext,
    riscv2zisk_context.Riscv2ZiskContext.load_op_typed,
    riscv2zisk_context.Riscv2ZiskContext.load_op_with_reg_offset,
    zisk_inst_builder.ZiskInstBuilder.new_for_rv64im_lowering,
    zisk_inst_builder.ZiskInstBuilder.new,
    zisk_inst_builder.ZiskInstBuilder.Insts.CoreDefaultDefault.default,
    zisk_inst.ZiskInst.Insts.CoreDefaultDefault.default,
    zisk_inst_builder.ZiskInstBuilder.src_a_imm,
    zisk_inst_builder.ZiskInstBuilder.src_a_reg,
    zisk_inst_builder.ZiskInstBuilder.ind_width,
    zisk_inst_builder.ZiskInstBuilder.src_b_ind,
    zisk_inst_builder.ZiskInstBuilder.op_zisk,
    zisk_ops.ZiskOp.op_type,
    zisk_ops.ZiskOp.code,
    zisk_ops.ZiskOp.input_size,
    zisk_ops.ZiskOp.is_m32,
    zisk_inst.ZiskOperationType.Insts.CoreConvertFromOpType.from,
    zisk_inst_builder.ZiskInstBuilder.set_runtime_op_fields,
    zisk_inst_builder.ZiskInstBuilder.store_reg,
    zisk_inst_builder.ZiskInstBuilder.j,
    zisk_inst_builder.ZiskInstBuilder.build,
    riscv2zisk_context.Riscv2ZiskContext.insert_inst,
    zisk_registers.REGS_IN_MAIN_FROM,
    zisk_registers.REGS_IN_MAIN_TO,
    zisk_registers.REG_FIRST,
    mem.SYS_ADDR,
    mem.RAM_ADDR,
    u64_mk_ofNat_val,
    i64_mk_ofNat_val,
    UScalar.cast,
    UScalar.hcast,
    IScalar.cast,
    IScalar.hcast,
    UScalar.add,
    IScalar.add,
    UScalar.tryMk,
    IScalar.tryMk,
    UScalar.tryMkOpt,
    IScalar.tryMkOpt,
    Result.ofOption,
    lift,
    regs_from_set_width_u64_val_eq,
    regs_to_set_width_u64_val_eq,
    regs_from_set_width_i64_val_eq,
    regs_to_set_width_i64_val_eq,
    u64_add_zero_ok,
    i64_add_zero_ok,
    u64_zero_eq_zero,
    u64_zero_shift_right_32_ok,
    i64_zero_eq_zero,
    one_u64_scalar_ne_zero,
    one_i64_scalar_ne_zero,
    u64_one_val_ne_zero,
    u64_one_val_not_gt_regs_to,
    u64_31_ne_zero,
    u64_31_val_ne_zero,
    u64_31_val_not_gt_regs_to,
    i64_one_val_not_lt_regs_from,
    i64_one_val_not_gt_regs_to,
    i64_31_ne_zero,
    i64_31_val_not_lt_regs_from,
    i64_31_val_not_gt_regs_to,
    one_u64_val_not_lt_regs_from_set_width,
    regs_to_set_width_val_not_lt_one_u64,
    one_i64_val_not_lt_regs_from_set_width,
    regs_to_set_width_val_not_lt_one_i64]

set_option maxHeartbeats 2000000 in
theorem all_load_width2_symbolic_imm_materializes_result_flag
    (imm : Std.I32) :
    allRvU32Regs.all
      (fun rd =>
        allRvU32Regs.all
          (fun rs1 =>
            helperMaterializesResultFlag
              (fun ctx =>
                riscv2zisk_context.Riscv2ZiskContext.load_op_typed
                  ctx
                  { rom_address := 0#u64, rd := rd, rs1 := rs1,
                    rs2 := 0#u32, imm := imm }
                  zisk_ops.ZiskOp.Add 2#u64 4#u64))) = true := by
  rw [u64_2_eq_pattern]
  simp [allRvU32Regs, helperMaterializesResultFlag, helperMaterializesResult,
    emptyExtractContext,
    riscv2zisk_context.Riscv2ZiskContext.load_op_typed,
    riscv2zisk_context.Riscv2ZiskContext.load_op_with_reg_offset,
    zisk_inst_builder.ZiskInstBuilder.new_for_rv64im_lowering,
    zisk_inst_builder.ZiskInstBuilder.new,
    zisk_inst_builder.ZiskInstBuilder.Insts.CoreDefaultDefault.default,
    zisk_inst.ZiskInst.Insts.CoreDefaultDefault.default,
    zisk_inst_builder.ZiskInstBuilder.src_a_imm,
    zisk_inst_builder.ZiskInstBuilder.src_a_reg,
    zisk_inst_builder.ZiskInstBuilder.ind_width,
    zisk_inst_builder.ZiskInstBuilder.src_b_ind,
    zisk_inst_builder.ZiskInstBuilder.op_zisk,
    zisk_ops.ZiskOp.op_type,
    zisk_ops.ZiskOp.code,
    zisk_ops.ZiskOp.input_size,
    zisk_ops.ZiskOp.is_m32,
    zisk_inst.ZiskOperationType.Insts.CoreConvertFromOpType.from,
    zisk_inst_builder.ZiskInstBuilder.set_runtime_op_fields,
    zisk_inst_builder.ZiskInstBuilder.store_reg,
    zisk_inst_builder.ZiskInstBuilder.j,
    zisk_inst_builder.ZiskInstBuilder.build,
    riscv2zisk_context.Riscv2ZiskContext.insert_inst,
    zisk_registers.REGS_IN_MAIN_FROM,
    zisk_registers.REGS_IN_MAIN_TO,
    zisk_registers.REG_FIRST,
    mem.SYS_ADDR,
    mem.RAM_ADDR,
    u64_mk_ofNat_val,
    i64_mk_ofNat_val,
    UScalar.cast,
    UScalar.hcast,
    IScalar.cast,
    IScalar.hcast,
    UScalar.add,
    IScalar.add,
    UScalar.tryMk,
    IScalar.tryMk,
    UScalar.tryMkOpt,
    IScalar.tryMkOpt,
    Result.ofOption,
    lift,
    regs_from_set_width_u64_val_eq,
    regs_to_set_width_u64_val_eq,
    regs_from_set_width_i64_val_eq,
    regs_to_set_width_i64_val_eq,
    u64_add_zero_ok,
    i64_add_zero_ok,
    u64_zero_eq_zero,
    u64_zero_shift_right_32_ok,
    i64_zero_eq_zero,
    one_u64_scalar_ne_zero,
    one_i64_scalar_ne_zero,
    u64_one_val_ne_zero,
    u64_one_val_not_gt_regs_to,
    u64_31_ne_zero,
    u64_31_val_ne_zero,
    u64_31_val_not_gt_regs_to,
    i64_one_val_not_lt_regs_from,
    i64_one_val_not_gt_regs_to,
    i64_31_ne_zero,
    i64_31_val_not_lt_regs_from,
    i64_31_val_not_gt_regs_to,
    one_u64_val_not_lt_regs_from_set_width,
    regs_to_set_width_val_not_lt_one_u64,
    one_i64_val_not_lt_regs_from_set_width,
    regs_to_set_width_val_not_lt_one_i64]

set_option maxHeartbeats 2000000 in
theorem all_load_width4_symbolic_imm_materializes_result_flag
    (imm : Std.I32) :
    allRvU32Regs.all
      (fun rd =>
        allRvU32Regs.all
          (fun rs1 =>
            helperMaterializesResultFlag
              (fun ctx =>
                riscv2zisk_context.Riscv2ZiskContext.load_op_typed
                  ctx
                  { rom_address := 0#u64, rd := rd, rs1 := rs1,
                    rs2 := 0#u32, imm := imm }
                  zisk_ops.ZiskOp.Add 4#u64 4#u64))) = true := by
  rw [u64_4_eq_pattern]
  simp [allRvU32Regs, helperMaterializesResultFlag, helperMaterializesResult,
    emptyExtractContext,
    riscv2zisk_context.Riscv2ZiskContext.load_op_typed,
    riscv2zisk_context.Riscv2ZiskContext.load_op_with_reg_offset,
    zisk_inst_builder.ZiskInstBuilder.new_for_rv64im_lowering,
    zisk_inst_builder.ZiskInstBuilder.new,
    zisk_inst_builder.ZiskInstBuilder.Insts.CoreDefaultDefault.default,
    zisk_inst.ZiskInst.Insts.CoreDefaultDefault.default,
    zisk_inst_builder.ZiskInstBuilder.src_a_imm,
    zisk_inst_builder.ZiskInstBuilder.src_a_reg,
    zisk_inst_builder.ZiskInstBuilder.ind_width,
    zisk_inst_builder.ZiskInstBuilder.src_b_ind,
    zisk_inst_builder.ZiskInstBuilder.op_zisk,
    zisk_ops.ZiskOp.op_type,
    zisk_ops.ZiskOp.code,
    zisk_ops.ZiskOp.input_size,
    zisk_ops.ZiskOp.is_m32,
    zisk_inst.ZiskOperationType.Insts.CoreConvertFromOpType.from,
    zisk_inst_builder.ZiskInstBuilder.set_runtime_op_fields,
    zisk_inst_builder.ZiskInstBuilder.store_reg,
    zisk_inst_builder.ZiskInstBuilder.j,
    zisk_inst_builder.ZiskInstBuilder.build,
    riscv2zisk_context.Riscv2ZiskContext.insert_inst,
    zisk_registers.REGS_IN_MAIN_FROM,
    zisk_registers.REGS_IN_MAIN_TO,
    zisk_registers.REG_FIRST,
    mem.SYS_ADDR,
    mem.RAM_ADDR,
    u64_mk_ofNat_val,
    i64_mk_ofNat_val,
    UScalar.cast,
    UScalar.hcast,
    IScalar.cast,
    IScalar.hcast,
    UScalar.add,
    IScalar.add,
    UScalar.tryMk,
    IScalar.tryMk,
    UScalar.tryMkOpt,
    IScalar.tryMkOpt,
    Result.ofOption,
    lift,
    regs_from_set_width_u64_val_eq,
    regs_to_set_width_u64_val_eq,
    regs_from_set_width_i64_val_eq,
    regs_to_set_width_i64_val_eq,
    u64_add_zero_ok,
    i64_add_zero_ok,
    u64_zero_eq_zero,
    u64_zero_shift_right_32_ok,
    i64_zero_eq_zero,
    one_u64_scalar_ne_zero,
    one_i64_scalar_ne_zero,
    u64_one_val_ne_zero,
    u64_one_val_not_gt_regs_to,
    u64_31_ne_zero,
    u64_31_val_ne_zero,
    u64_31_val_not_gt_regs_to,
    i64_one_val_not_lt_regs_from,
    i64_one_val_not_gt_regs_to,
    i64_31_ne_zero,
    i64_31_val_not_lt_regs_from,
    i64_31_val_not_gt_regs_to,
    one_u64_val_not_lt_regs_from_set_width,
    regs_to_set_width_val_not_lt_one_u64,
    one_i64_val_not_lt_regs_from_set_width,
    regs_to_set_width_val_not_lt_one_i64]

set_option maxHeartbeats 2000000 in
theorem all_load_width8_symbolic_imm_materializes_result_flag
    (imm : Std.I32) :
    allRvU32Regs.all
      (fun rd =>
        allRvU32Regs.all
          (fun rs1 =>
            helperMaterializesResultFlag
              (fun ctx =>
                riscv2zisk_context.Riscv2ZiskContext.load_op_typed
                  ctx
                  { rom_address := 0#u64, rd := rd, rs1 := rs1,
                    rs2 := 0#u32, imm := imm }
                  zisk_ops.ZiskOp.Add 8#u64 4#u64))) = true := by
  rw [u64_8_eq_pattern]
  simp [allRvU32Regs, helperMaterializesResultFlag, helperMaterializesResult,
    emptyExtractContext,
    riscv2zisk_context.Riscv2ZiskContext.load_op_typed,
    riscv2zisk_context.Riscv2ZiskContext.load_op_with_reg_offset,
    zisk_inst_builder.ZiskInstBuilder.new_for_rv64im_lowering,
    zisk_inst_builder.ZiskInstBuilder.new,
    zisk_inst_builder.ZiskInstBuilder.Insts.CoreDefaultDefault.default,
    zisk_inst.ZiskInst.Insts.CoreDefaultDefault.default,
    zisk_inst_builder.ZiskInstBuilder.src_a_imm,
    zisk_inst_builder.ZiskInstBuilder.src_a_reg,
    zisk_inst_builder.ZiskInstBuilder.ind_width,
    zisk_inst_builder.ZiskInstBuilder.src_b_ind,
    zisk_inst_builder.ZiskInstBuilder.op_zisk,
    zisk_ops.ZiskOp.op_type,
    zisk_ops.ZiskOp.code,
    zisk_ops.ZiskOp.input_size,
    zisk_ops.ZiskOp.is_m32,
    zisk_inst.ZiskOperationType.Insts.CoreConvertFromOpType.from,
    zisk_inst_builder.ZiskInstBuilder.set_runtime_op_fields,
    zisk_inst_builder.ZiskInstBuilder.store_reg,
    zisk_inst_builder.ZiskInstBuilder.j,
    zisk_inst_builder.ZiskInstBuilder.build,
    riscv2zisk_context.Riscv2ZiskContext.insert_inst,
    zisk_registers.REGS_IN_MAIN_FROM,
    zisk_registers.REGS_IN_MAIN_TO,
    zisk_registers.REG_FIRST,
    mem.SYS_ADDR,
    mem.RAM_ADDR,
    u64_mk_ofNat_val,
    i64_mk_ofNat_val,
    UScalar.cast,
    UScalar.hcast,
    IScalar.cast,
    IScalar.hcast,
    UScalar.add,
    IScalar.add,
    UScalar.tryMk,
    IScalar.tryMk,
    UScalar.tryMkOpt,
    IScalar.tryMkOpt,
    Result.ofOption,
    lift,
    regs_from_set_width_u64_val_eq,
    regs_to_set_width_u64_val_eq,
    regs_from_set_width_i64_val_eq,
    regs_to_set_width_i64_val_eq,
    u64_add_zero_ok,
    i64_add_zero_ok,
    u64_zero_eq_zero,
    u64_zero_shift_right_32_ok,
    i64_zero_eq_zero,
    one_u64_scalar_ne_zero,
    one_i64_scalar_ne_zero,
    u64_one_val_ne_zero,
    u64_one_val_not_gt_regs_to,
    u64_31_ne_zero,
    u64_31_val_ne_zero,
    u64_31_val_not_gt_regs_to,
    i64_one_val_not_lt_regs_from,
    i64_one_val_not_gt_regs_to,
    i64_31_ne_zero,
    i64_31_val_not_lt_regs_from,
    i64_31_val_not_gt_regs_to,
    one_u64_val_not_lt_regs_from_set_width,
    regs_to_set_width_val_not_lt_one_u64,
    one_i64_val_not_lt_regs_from_set_width,
    regs_to_set_width_val_not_lt_one_i64]

/-- The extracted load helper materializes a row for symbolic immediates on
ordinary-register paths. This lifts the earlier representative checks past the
generated scalar `rd + reg_offset` step. -/
theorem empty_load_width1_reg1_symbolic_imm_materializes_result_flag
    (imm : Std.I32) :
    helperMaterializesResultFlag
      (fun ctx =>
        riscv2zisk_context.Riscv2ZiskContext.load_op_typed
          ctx
          { rom_address := 0#u64, rd := 1#u32, rs1 := 1#u32,
            rs2 := 0#u32, imm := imm }
          zisk_ops.ZiskOp.Add 1#u64 4#u64) = true := by
  rw [u64_1_eq_pattern]
  simp [helperMaterializesResultFlag, helperMaterializesResult, emptyExtractContext,
    riscv2zisk_context.Riscv2ZiskContext.load_op_typed,
    riscv2zisk_context.Riscv2ZiskContext.load_op_with_reg_offset,
    zisk_inst_builder.ZiskInstBuilder.new_for_rv64im_lowering,
    zisk_inst_builder.ZiskInstBuilder.new,
    zisk_inst_builder.ZiskInstBuilder.Insts.CoreDefaultDefault.default,
    zisk_inst.ZiskInst.Insts.CoreDefaultDefault.default,
    zisk_inst_builder.ZiskInstBuilder.src_a_reg,
    zisk_inst_builder.ZiskInstBuilder.ind_width,
    zisk_inst_builder.ZiskInstBuilder.src_b_ind,
    zisk_inst_builder.ZiskInstBuilder.op_zisk,
    zisk_ops.ZiskOp.op_type,
    zisk_ops.ZiskOp.code,
    zisk_ops.ZiskOp.input_size,
    zisk_ops.ZiskOp.is_m32,
    zisk_inst.ZiskOperationType.Insts.CoreConvertFromOpType.from,
    zisk_inst_builder.ZiskInstBuilder.set_runtime_op_fields,
    zisk_inst_builder.ZiskInstBuilder.store_reg,
    zisk_inst_builder.ZiskInstBuilder.j,
    zisk_inst_builder.ZiskInstBuilder.build,
    riscv2zisk_context.Riscv2ZiskContext.insert_inst,
    zisk_registers.REGS_IN_MAIN_FROM,
    zisk_registers.REGS_IN_MAIN_TO,
    zisk_registers.REG_FIRST,
    mem.SYS_ADDR,
    mem.RAM_ADDR,
    UScalar.cast,
    UScalar.hcast,
    IScalar.hcast,
    i64_one_add_zero_ok,
    lift,
    one_u64_scalar_ne_zero,
    one_i64_scalar_ne_zero,
    one_u64_val_not_lt_regs_from_set_width,
    regs_to_set_width_val_not_lt_one_u64,
    one_i64_val_not_lt_regs_from_set_width,
    regs_to_set_width_val_not_lt_one_i64]

theorem empty_load_width2_reg1_symbolic_imm_materializes_result_flag
    (imm : Std.I32) :
    helperMaterializesResultFlag
      (fun ctx =>
        riscv2zisk_context.Riscv2ZiskContext.load_op_typed
          ctx
          { rom_address := 0#u64, rd := 1#u32, rs1 := 1#u32,
            rs2 := 0#u32, imm := imm }
          zisk_ops.ZiskOp.Add 2#u64 4#u64) = true := by
  rw [u64_2_eq_pattern]
  simp [helperMaterializesResultFlag, helperMaterializesResult, emptyExtractContext,
    riscv2zisk_context.Riscv2ZiskContext.load_op_typed,
    riscv2zisk_context.Riscv2ZiskContext.load_op_with_reg_offset,
    zisk_inst_builder.ZiskInstBuilder.new_for_rv64im_lowering,
    zisk_inst_builder.ZiskInstBuilder.new,
    zisk_inst_builder.ZiskInstBuilder.Insts.CoreDefaultDefault.default,
    zisk_inst.ZiskInst.Insts.CoreDefaultDefault.default,
    zisk_inst_builder.ZiskInstBuilder.src_a_reg,
    zisk_inst_builder.ZiskInstBuilder.ind_width,
    zisk_inst_builder.ZiskInstBuilder.src_b_ind,
    zisk_inst_builder.ZiskInstBuilder.op_zisk,
    zisk_ops.ZiskOp.op_type,
    zisk_ops.ZiskOp.code,
    zisk_ops.ZiskOp.input_size,
    zisk_ops.ZiskOp.is_m32,
    zisk_inst.ZiskOperationType.Insts.CoreConvertFromOpType.from,
    zisk_inst_builder.ZiskInstBuilder.set_runtime_op_fields,
    zisk_inst_builder.ZiskInstBuilder.store_reg,
    zisk_inst_builder.ZiskInstBuilder.j,
    zisk_inst_builder.ZiskInstBuilder.build,
    riscv2zisk_context.Riscv2ZiskContext.insert_inst,
    zisk_registers.REGS_IN_MAIN_FROM,
    zisk_registers.REGS_IN_MAIN_TO,
    zisk_registers.REG_FIRST,
    mem.SYS_ADDR,
    mem.RAM_ADDR,
    UScalar.cast,
    UScalar.hcast,
    IScalar.hcast,
    i64_one_add_zero_ok,
    lift,
    one_u64_scalar_ne_zero,
    one_i64_scalar_ne_zero,
    one_u64_val_not_lt_regs_from_set_width,
    regs_to_set_width_val_not_lt_one_u64,
    one_i64_val_not_lt_regs_from_set_width,
    regs_to_set_width_val_not_lt_one_i64]

theorem empty_load_width4_reg1_symbolic_imm_materializes_result_flag
    (imm : Std.I32) :
    helperMaterializesResultFlag
      (fun ctx =>
        riscv2zisk_context.Riscv2ZiskContext.load_op_typed
          ctx
          { rom_address := 0#u64, rd := 1#u32, rs1 := 1#u32,
            rs2 := 0#u32, imm := imm }
          zisk_ops.ZiskOp.Add 4#u64 4#u64) = true := by
  rw [u64_4_eq_pattern]
  simp [helperMaterializesResultFlag, helperMaterializesResult, emptyExtractContext,
    riscv2zisk_context.Riscv2ZiskContext.load_op_typed,
    riscv2zisk_context.Riscv2ZiskContext.load_op_with_reg_offset,
    zisk_inst_builder.ZiskInstBuilder.new_for_rv64im_lowering,
    zisk_inst_builder.ZiskInstBuilder.new,
    zisk_inst_builder.ZiskInstBuilder.Insts.CoreDefaultDefault.default,
    zisk_inst.ZiskInst.Insts.CoreDefaultDefault.default,
    zisk_inst_builder.ZiskInstBuilder.src_a_reg,
    zisk_inst_builder.ZiskInstBuilder.ind_width,
    zisk_inst_builder.ZiskInstBuilder.src_b_ind,
    zisk_inst_builder.ZiskInstBuilder.op_zisk,
    zisk_ops.ZiskOp.op_type,
    zisk_ops.ZiskOp.code,
    zisk_ops.ZiskOp.input_size,
    zisk_ops.ZiskOp.is_m32,
    zisk_inst.ZiskOperationType.Insts.CoreConvertFromOpType.from,
    zisk_inst_builder.ZiskInstBuilder.set_runtime_op_fields,
    zisk_inst_builder.ZiskInstBuilder.store_reg,
    zisk_inst_builder.ZiskInstBuilder.j,
    zisk_inst_builder.ZiskInstBuilder.build,
    riscv2zisk_context.Riscv2ZiskContext.insert_inst,
    zisk_registers.REGS_IN_MAIN_FROM,
    zisk_registers.REGS_IN_MAIN_TO,
    zisk_registers.REG_FIRST,
    mem.SYS_ADDR,
    mem.RAM_ADDR,
    UScalar.cast,
    UScalar.hcast,
    IScalar.hcast,
    i64_one_add_zero_ok,
    lift,
    one_u64_scalar_ne_zero,
    one_i64_scalar_ne_zero,
    one_u64_val_not_lt_regs_from_set_width,
    regs_to_set_width_val_not_lt_one_u64,
    one_i64_val_not_lt_regs_from_set_width,
    regs_to_set_width_val_not_lt_one_i64]

theorem empty_load_width8_reg1_symbolic_imm_materializes_result_flag
    (imm : Std.I32) :
    helperMaterializesResultFlag
      (fun ctx =>
        riscv2zisk_context.Riscv2ZiskContext.load_op_typed
          ctx
          { rom_address := 0#u64, rd := 1#u32, rs1 := 1#u32,
            rs2 := 0#u32, imm := imm }
          zisk_ops.ZiskOp.Add 8#u64 4#u64) = true := by
  rw [u64_8_eq_pattern]
  simp [helperMaterializesResultFlag, helperMaterializesResult, emptyExtractContext,
    riscv2zisk_context.Riscv2ZiskContext.load_op_typed,
    riscv2zisk_context.Riscv2ZiskContext.load_op_with_reg_offset,
    zisk_inst_builder.ZiskInstBuilder.new_for_rv64im_lowering,
    zisk_inst_builder.ZiskInstBuilder.new,
    zisk_inst_builder.ZiskInstBuilder.Insts.CoreDefaultDefault.default,
    zisk_inst.ZiskInst.Insts.CoreDefaultDefault.default,
    zisk_inst_builder.ZiskInstBuilder.src_a_reg,
    zisk_inst_builder.ZiskInstBuilder.ind_width,
    zisk_inst_builder.ZiskInstBuilder.src_b_ind,
    zisk_inst_builder.ZiskInstBuilder.op_zisk,
    zisk_ops.ZiskOp.op_type,
    zisk_ops.ZiskOp.code,
    zisk_ops.ZiskOp.input_size,
    zisk_ops.ZiskOp.is_m32,
    zisk_inst.ZiskOperationType.Insts.CoreConvertFromOpType.from,
    zisk_inst_builder.ZiskInstBuilder.set_runtime_op_fields,
    zisk_inst_builder.ZiskInstBuilder.store_reg,
    zisk_inst_builder.ZiskInstBuilder.j,
    zisk_inst_builder.ZiskInstBuilder.build,
    riscv2zisk_context.Riscv2ZiskContext.insert_inst,
    zisk_registers.REGS_IN_MAIN_FROM,
    zisk_registers.REGS_IN_MAIN_TO,
    zisk_registers.REG_FIRST,
    mem.SYS_ADDR,
    mem.RAM_ADDR,
    UScalar.cast,
    UScalar.hcast,
    IScalar.hcast,
    i64_one_add_zero_ok,
    lift,
    one_u64_scalar_ne_zero,
    one_i64_scalar_ne_zero,
    one_u64_val_not_lt_regs_from_set_width,
    regs_to_set_width_val_not_lt_one_u64,
    one_i64_val_not_lt_regs_from_set_width,
    regs_to_set_width_val_not_lt_one_i64]

/-- Production store-helper materialization milestones for each indirect memory
width used by RV64IM store opcodes. -/
theorem empty_store_width1_reg1_materializes_result_flag :
    helperMaterializesResultFlag
      (fun ctx =>
        riscv2zisk_context.Riscv2ZiskContext.store_op_typed
          ctx
          { rom_address := 0#u64, rd := 0#u32, rs1 := 1#u32,
            rs2 := 1#u32, imm := 0#i32 }
          zisk_ops.ZiskOp.Add 1#u64 4#u64) = true := by
  native_decide

theorem empty_store_width2_reg1_materializes_result_flag :
    helperMaterializesResultFlag
      (fun ctx =>
        riscv2zisk_context.Riscv2ZiskContext.store_op_typed
          ctx
          { rom_address := 0#u64, rd := 0#u32, rs1 := 1#u32,
            rs2 := 1#u32, imm := 0#i32 }
          zisk_ops.ZiskOp.Add 2#u64 4#u64) = true := by
  native_decide

theorem empty_store_width4_reg1_materializes_result_flag :
    helperMaterializesResultFlag
      (fun ctx =>
        riscv2zisk_context.Riscv2ZiskContext.store_op_typed
          ctx
          { rom_address := 0#u64, rd := 0#u32, rs1 := 1#u32,
            rs2 := 1#u32, imm := 0#i32 }
          zisk_ops.ZiskOp.Add 4#u64 4#u64) = true := by
  native_decide

theorem empty_store_width8_reg1_materializes_result_flag :
    helperMaterializesResultFlag
      (fun ctx =>
        riscv2zisk_context.Riscv2ZiskContext.store_op_typed
          ctx
          { rom_address := 0#u64, rd := 0#u32, rs1 := 1#u32,
            rs2 := 1#u32, imm := 0#i32 }
          zisk_ops.ZiskOp.Add 8#u64 4#u64) = true := by
  native_decide

/- Edge-register symbolic-immediate store-helper materialization. This probes
both x0 routing and ordinary-register routing through the extracted production
store helper without enumerating the full `rs1 × rs2` grid yet. -/
set_option maxHeartbeats 2000000 in
theorem edge_store_width1_symbolic_imm_materializes_result_flag
    (imm : Std.I32) :
    edgeRvU32Regs.all
      (fun rs1 =>
        edgeRvU32Regs.all
          (fun rs2 =>
            helperMaterializesResultFlag
              (fun ctx =>
                riscv2zisk_context.Riscv2ZiskContext.store_op_typed
                  ctx
                  { rom_address := 0#u64, rd := 0#u32, rs1 := rs1,
                    rs2 := rs2, imm := imm }
                  zisk_ops.ZiskOp.Add 1#u64 4#u64))) = true := by
  rw [u64_1_eq_pattern]
  simp [edgeRvU32Regs, helperMaterializesResultFlag, helperMaterializesResult,
    emptyExtractContext,
    riscv2zisk_context.Riscv2ZiskContext.store_op_typed,
    riscv2zisk_context.Riscv2ZiskContext.store_op_with_reg_offset,
    src_b_imm_zero_flag,
    src_b_imm_zero_ok_true,
    zisk_inst_builder.ZiskInstBuilder.new_for_rv64im_lowering,
    zisk_inst_builder.ZiskInstBuilder.new,
    zisk_inst_builder.ZiskInstBuilder.Insts.CoreDefaultDefault.default,
    zisk_inst.ZiskInst.Insts.CoreDefaultDefault.default,
    zisk_inst_builder.ZiskInstBuilder.src_a_imm,
    zisk_inst_builder.ZiskInstBuilder.src_a_reg,
    zisk_inst_builder.ZiskInstBuilder.src_b_imm,
    zisk_inst_builder.ZiskInstBuilder.src_b_reg,
    zisk_inst_builder.ZiskInstBuilder.op_zisk,
    zisk_ops.ZiskOp.op_type,
    zisk_ops.ZiskOp.code,
    zisk_ops.ZiskOp.input_size,
    zisk_ops.ZiskOp.is_m32,
    zisk_inst.ZiskOperationType.Insts.CoreConvertFromOpType.from,
    zisk_inst_builder.ZiskInstBuilder.set_runtime_op_fields,
    zisk_inst_builder.ZiskInstBuilder.ind_width,
    zisk_inst_builder.ZiskInstBuilder.store_ind,
    zisk_inst_builder.ZiskInstBuilder.j,
    zisk_inst_builder.ZiskInstBuilder.build,
    riscv2zisk_context.Riscv2ZiskContext.insert_inst,
    zisk_registers.REGS_IN_MAIN_FROM,
    zisk_registers.REGS_IN_MAIN_TO,
    zisk_registers.REG_FIRST,
    mem.SYS_ADDR,
    mem.RAM_ADDR,
    UScalar.cast,
    UScalar.hcast,
    IScalar.cast,
    IScalar.hcast,
    lift,
    regs_from_set_width_u64_val_eq,
    regs_to_set_width_u64_val_eq,
    regs_from_set_width_i64_val_eq,
    regs_to_set_width_i64_val_eq,
    u64_add_zero_ok,
    i64_add_zero_ok,
    u64_zero_eq_zero,
    u64_zero_shift_right_32_ok,
    i64_zero_eq_zero,
    one_u64_scalar_ne_zero,
    one_i64_scalar_ne_zero,
    u64_one_val_ne_zero,
    u64_one_val_not_gt_regs_to,
    u64_31_ne_zero,
    u64_31_val_ne_zero,
    u64_31_val_not_gt_regs_to,
    i64_one_val_not_lt_regs_from,
    i64_one_val_not_gt_regs_to,
    i64_31_ne_zero,
    i64_31_val_not_lt_regs_from,
    i64_31_val_not_gt_regs_to,
    one_u64_val_not_lt_regs_from_set_width,
    regs_to_set_width_val_not_lt_one_u64,
    one_i64_val_not_lt_regs_from_set_width,
    regs_to_set_width_val_not_lt_one_i64]

set_option maxHeartbeats 2000000 in
theorem edge_store_width2_symbolic_imm_materializes_result_flag
    (imm : Std.I32) :
    edgeRvU32Regs.all
      (fun rs1 =>
        edgeRvU32Regs.all
          (fun rs2 =>
            helperMaterializesResultFlag
              (fun ctx =>
                riscv2zisk_context.Riscv2ZiskContext.store_op_typed
                  ctx
                  { rom_address := 0#u64, rd := 0#u32, rs1 := rs1,
                    rs2 := rs2, imm := imm }
                  zisk_ops.ZiskOp.Add 2#u64 4#u64))) = true := by
  rw [u64_2_eq_pattern]
  simp [edgeRvU32Regs, helperMaterializesResultFlag, helperMaterializesResult,
    emptyExtractContext,
    riscv2zisk_context.Riscv2ZiskContext.store_op_typed,
    riscv2zisk_context.Riscv2ZiskContext.store_op_with_reg_offset,
    src_b_imm_zero_flag,
    src_b_imm_zero_ok_true,
    zisk_inst_builder.ZiskInstBuilder.new_for_rv64im_lowering,
    zisk_inst_builder.ZiskInstBuilder.new,
    zisk_inst_builder.ZiskInstBuilder.Insts.CoreDefaultDefault.default,
    zisk_inst.ZiskInst.Insts.CoreDefaultDefault.default,
    zisk_inst_builder.ZiskInstBuilder.src_a_imm,
    zisk_inst_builder.ZiskInstBuilder.src_a_reg,
    zisk_inst_builder.ZiskInstBuilder.src_b_imm,
    zisk_inst_builder.ZiskInstBuilder.src_b_reg,
    zisk_inst_builder.ZiskInstBuilder.op_zisk,
    zisk_ops.ZiskOp.op_type,
    zisk_ops.ZiskOp.code,
    zisk_ops.ZiskOp.input_size,
    zisk_ops.ZiskOp.is_m32,
    zisk_inst.ZiskOperationType.Insts.CoreConvertFromOpType.from,
    zisk_inst_builder.ZiskInstBuilder.set_runtime_op_fields,
    zisk_inst_builder.ZiskInstBuilder.ind_width,
    zisk_inst_builder.ZiskInstBuilder.store_ind,
    zisk_inst_builder.ZiskInstBuilder.j,
    zisk_inst_builder.ZiskInstBuilder.build,
    riscv2zisk_context.Riscv2ZiskContext.insert_inst,
    zisk_registers.REGS_IN_MAIN_FROM,
    zisk_registers.REGS_IN_MAIN_TO,
    zisk_registers.REG_FIRST,
    mem.SYS_ADDR,
    mem.RAM_ADDR,
    UScalar.cast,
    UScalar.hcast,
    IScalar.cast,
    IScalar.hcast,
    lift,
    regs_from_set_width_u64_val_eq,
    regs_to_set_width_u64_val_eq,
    regs_from_set_width_i64_val_eq,
    regs_to_set_width_i64_val_eq,
    u64_add_zero_ok,
    i64_add_zero_ok,
    u64_zero_eq_zero,
    u64_zero_shift_right_32_ok,
    i64_zero_eq_zero,
    one_u64_scalar_ne_zero,
    one_i64_scalar_ne_zero,
    u64_one_val_ne_zero,
    u64_one_val_not_gt_regs_to,
    u64_31_ne_zero,
    u64_31_val_ne_zero,
    u64_31_val_not_gt_regs_to,
    i64_one_val_not_lt_regs_from,
    i64_one_val_not_gt_regs_to,
    i64_31_ne_zero,
    i64_31_val_not_lt_regs_from,
    i64_31_val_not_gt_regs_to,
    one_u64_val_not_lt_regs_from_set_width,
    regs_to_set_width_val_not_lt_one_u64,
    one_i64_val_not_lt_regs_from_set_width,
    regs_to_set_width_val_not_lt_one_i64]

set_option maxHeartbeats 2000000 in
theorem edge_store_width4_symbolic_imm_materializes_result_flag
    (imm : Std.I32) :
    edgeRvU32Regs.all
      (fun rs1 =>
        edgeRvU32Regs.all
          (fun rs2 =>
            helperMaterializesResultFlag
              (fun ctx =>
                riscv2zisk_context.Riscv2ZiskContext.store_op_typed
                  ctx
                  { rom_address := 0#u64, rd := 0#u32, rs1 := rs1,
                    rs2 := rs2, imm := imm }
                  zisk_ops.ZiskOp.Add 4#u64 4#u64))) = true := by
  rw [u64_4_eq_pattern]
  simp [edgeRvU32Regs, helperMaterializesResultFlag, helperMaterializesResult,
    emptyExtractContext,
    riscv2zisk_context.Riscv2ZiskContext.store_op_typed,
    riscv2zisk_context.Riscv2ZiskContext.store_op_with_reg_offset,
    src_b_imm_zero_flag,
    src_b_imm_zero_ok_true,
    zisk_inst_builder.ZiskInstBuilder.new_for_rv64im_lowering,
    zisk_inst_builder.ZiskInstBuilder.new,
    zisk_inst_builder.ZiskInstBuilder.Insts.CoreDefaultDefault.default,
    zisk_inst.ZiskInst.Insts.CoreDefaultDefault.default,
    zisk_inst_builder.ZiskInstBuilder.src_a_imm,
    zisk_inst_builder.ZiskInstBuilder.src_a_reg,
    zisk_inst_builder.ZiskInstBuilder.src_b_imm,
    zisk_inst_builder.ZiskInstBuilder.src_b_reg,
    zisk_inst_builder.ZiskInstBuilder.op_zisk,
    zisk_ops.ZiskOp.op_type,
    zisk_ops.ZiskOp.code,
    zisk_ops.ZiskOp.input_size,
    zisk_ops.ZiskOp.is_m32,
    zisk_inst.ZiskOperationType.Insts.CoreConvertFromOpType.from,
    zisk_inst_builder.ZiskInstBuilder.set_runtime_op_fields,
    zisk_inst_builder.ZiskInstBuilder.ind_width,
    zisk_inst_builder.ZiskInstBuilder.store_ind,
    zisk_inst_builder.ZiskInstBuilder.j,
    zisk_inst_builder.ZiskInstBuilder.build,
    riscv2zisk_context.Riscv2ZiskContext.insert_inst,
    zisk_registers.REGS_IN_MAIN_FROM,
    zisk_registers.REGS_IN_MAIN_TO,
    zisk_registers.REG_FIRST,
    mem.SYS_ADDR,
    mem.RAM_ADDR,
    UScalar.cast,
    UScalar.hcast,
    IScalar.cast,
    IScalar.hcast,
    lift,
    regs_from_set_width_u64_val_eq,
    regs_to_set_width_u64_val_eq,
    regs_from_set_width_i64_val_eq,
    regs_to_set_width_i64_val_eq,
    u64_add_zero_ok,
    i64_add_zero_ok,
    u64_zero_eq_zero,
    u64_zero_shift_right_32_ok,
    i64_zero_eq_zero,
    one_u64_scalar_ne_zero,
    one_i64_scalar_ne_zero,
    u64_one_val_ne_zero,
    u64_one_val_not_gt_regs_to,
    u64_31_ne_zero,
    u64_31_val_ne_zero,
    u64_31_val_not_gt_regs_to,
    i64_one_val_not_lt_regs_from,
    i64_one_val_not_gt_regs_to,
    i64_31_ne_zero,
    i64_31_val_not_lt_regs_from,
    i64_31_val_not_gt_regs_to,
    one_u64_val_not_lt_regs_from_set_width,
    regs_to_set_width_val_not_lt_one_u64,
    one_i64_val_not_lt_regs_from_set_width,
    regs_to_set_width_val_not_lt_one_i64]

set_option maxHeartbeats 2000000 in
theorem edge_store_width8_symbolic_imm_materializes_result_flag
    (imm : Std.I32) :
    edgeRvU32Regs.all
      (fun rs1 =>
        edgeRvU32Regs.all
          (fun rs2 =>
            helperMaterializesResultFlag
              (fun ctx =>
                riscv2zisk_context.Riscv2ZiskContext.store_op_typed
                  ctx
                  { rom_address := 0#u64, rd := 0#u32, rs1 := rs1,
                    rs2 := rs2, imm := imm }
                  zisk_ops.ZiskOp.Add 8#u64 4#u64))) = true := by
  rw [u64_8_eq_pattern]
  simp [edgeRvU32Regs, helperMaterializesResultFlag, helperMaterializesResult,
    emptyExtractContext,
    riscv2zisk_context.Riscv2ZiskContext.store_op_typed,
    riscv2zisk_context.Riscv2ZiskContext.store_op_with_reg_offset,
    src_b_imm_zero_flag,
    src_b_imm_zero_ok_true,
    zisk_inst_builder.ZiskInstBuilder.new_for_rv64im_lowering,
    zisk_inst_builder.ZiskInstBuilder.new,
    zisk_inst_builder.ZiskInstBuilder.Insts.CoreDefaultDefault.default,
    zisk_inst.ZiskInst.Insts.CoreDefaultDefault.default,
    zisk_inst_builder.ZiskInstBuilder.src_a_imm,
    zisk_inst_builder.ZiskInstBuilder.src_a_reg,
    zisk_inst_builder.ZiskInstBuilder.src_b_imm,
    zisk_inst_builder.ZiskInstBuilder.src_b_reg,
    zisk_inst_builder.ZiskInstBuilder.op_zisk,
    zisk_ops.ZiskOp.op_type,
    zisk_ops.ZiskOp.code,
    zisk_ops.ZiskOp.input_size,
    zisk_ops.ZiskOp.is_m32,
    zisk_inst.ZiskOperationType.Insts.CoreConvertFromOpType.from,
    zisk_inst_builder.ZiskInstBuilder.set_runtime_op_fields,
    zisk_inst_builder.ZiskInstBuilder.ind_width,
    zisk_inst_builder.ZiskInstBuilder.store_ind,
    zisk_inst_builder.ZiskInstBuilder.j,
    zisk_inst_builder.ZiskInstBuilder.build,
    riscv2zisk_context.Riscv2ZiskContext.insert_inst,
    zisk_registers.REGS_IN_MAIN_FROM,
    zisk_registers.REGS_IN_MAIN_TO,
    zisk_registers.REG_FIRST,
    mem.SYS_ADDR,
    mem.RAM_ADDR,
    UScalar.cast,
    UScalar.hcast,
    IScalar.cast,
    IScalar.hcast,
    lift,
    regs_from_set_width_u64_val_eq,
    regs_to_set_width_u64_val_eq,
    regs_from_set_width_i64_val_eq,
    regs_to_set_width_i64_val_eq,
    u64_add_zero_ok,
    i64_add_zero_ok,
    u64_zero_eq_zero,
    u64_zero_shift_right_32_ok,
    i64_zero_eq_zero,
    one_u64_scalar_ne_zero,
    one_i64_scalar_ne_zero,
    u64_one_val_ne_zero,
    u64_one_val_not_gt_regs_to,
    u64_31_ne_zero,
    u64_31_val_ne_zero,
    u64_31_val_not_gt_regs_to,
    i64_one_val_not_lt_regs_from,
    i64_one_val_not_gt_regs_to,
    i64_31_ne_zero,
    i64_31_val_not_lt_regs_from,
    i64_31_val_not_gt_regs_to,
    one_u64_val_not_lt_regs_from_set_width,
    regs_to_set_width_val_not_lt_one_u64,
    one_i64_val_not_lt_regs_from_set_width,
    regs_to_set_width_val_not_lt_one_i64]

/- Full `rs1 × rs2` symbolic-immediate store-helper materialization. This
extends the edge-register store checks across every RV source-register pair. -/
set_option maxHeartbeats 4000000 in
theorem all_store_width1_symbolic_imm_materializes_result_flag
    (imm : Std.I32) :
    allRvU32Regs.all
      (fun rs1 =>
        allRvU32Regs.all
          (fun rs2 =>
            helperMaterializesResultFlag
              (fun ctx =>
                riscv2zisk_context.Riscv2ZiskContext.store_op_typed
                  ctx
                  { rom_address := 0#u64, rd := 0#u32, rs1 := rs1,
                    rs2 := rs2, imm := imm }
                  zisk_ops.ZiskOp.Add 1#u64 4#u64))) = true := by
  rw [u64_1_eq_pattern]
  simp [allRvU32Regs, helperMaterializesResultFlag, helperMaterializesResult,
    emptyExtractContext,
    riscv2zisk_context.Riscv2ZiskContext.store_op_typed,
    riscv2zisk_context.Riscv2ZiskContext.store_op_with_reg_offset,
    src_b_imm_zero_ok_true,
    zisk_inst_builder.ZiskInstBuilder.new_for_rv64im_lowering,
    zisk_inst_builder.ZiskInstBuilder.new,
    zisk_inst_builder.ZiskInstBuilder.Insts.CoreDefaultDefault.default,
    zisk_inst.ZiskInst.Insts.CoreDefaultDefault.default,
    zisk_inst_builder.ZiskInstBuilder.src_a_imm,
    zisk_inst_builder.ZiskInstBuilder.src_a_reg,
    zisk_inst_builder.ZiskInstBuilder.src_b_imm,
    zisk_inst_builder.ZiskInstBuilder.src_b_reg,
    zisk_inst_builder.ZiskInstBuilder.op_zisk,
    zisk_ops.ZiskOp.op_type,
    zisk_ops.ZiskOp.code,
    zisk_ops.ZiskOp.input_size,
    zisk_ops.ZiskOp.is_m32,
    zisk_inst.ZiskOperationType.Insts.CoreConvertFromOpType.from,
    zisk_inst_builder.ZiskInstBuilder.set_runtime_op_fields,
    zisk_inst_builder.ZiskInstBuilder.ind_width,
    zisk_inst_builder.ZiskInstBuilder.store_ind,
    zisk_inst_builder.ZiskInstBuilder.j,
    zisk_inst_builder.ZiskInstBuilder.build,
    riscv2zisk_context.Riscv2ZiskContext.insert_inst,
    zisk_registers.REGS_IN_MAIN_FROM,
    zisk_registers.REGS_IN_MAIN_TO,
    zisk_registers.REG_FIRST,
    mem.SYS_ADDR,
    mem.RAM_ADDR,
    u64_mk_ofNat_val,
    i64_mk_ofNat_val,
    UScalar.cast,
    UScalar.hcast,
    IScalar.cast,
    IScalar.hcast,
    lift,
    regs_from_set_width_u64_val_eq,
    regs_to_set_width_u64_val_eq,
    regs_from_set_width_i64_val_eq,
    regs_to_set_width_i64_val_eq,
    u64_add_zero_ok,
    i64_add_zero_ok,
    u64_zero_eq_zero,
    u64_zero_shift_right_32_ok,
    i64_zero_eq_zero,
    one_u64_scalar_ne_zero,
    one_i64_scalar_ne_zero,
    u64_one_val_ne_zero,
    u64_one_val_not_gt_regs_to,
    u64_31_ne_zero,
    u64_31_val_ne_zero,
    u64_31_val_not_gt_regs_to,
    i64_one_val_not_lt_regs_from,
    i64_one_val_not_gt_regs_to,
    i64_31_ne_zero,
    i64_31_val_not_lt_regs_from,
    i64_31_val_not_gt_regs_to,
    one_u64_val_not_lt_regs_from_set_width,
    regs_to_set_width_val_not_lt_one_u64,
    one_i64_val_not_lt_regs_from_set_width,
    regs_to_set_width_val_not_lt_one_i64]

set_option maxHeartbeats 4000000 in
theorem all_store_width2_symbolic_imm_materializes_result_flag
    (imm : Std.I32) :
    allRvU32Regs.all
      (fun rs1 =>
        allRvU32Regs.all
          (fun rs2 =>
            helperMaterializesResultFlag
              (fun ctx =>
                riscv2zisk_context.Riscv2ZiskContext.store_op_typed
                  ctx
                  { rom_address := 0#u64, rd := 0#u32, rs1 := rs1,
                    rs2 := rs2, imm := imm }
                  zisk_ops.ZiskOp.Add 2#u64 4#u64))) = true := by
  rw [u64_2_eq_pattern]
  simp [allRvU32Regs, helperMaterializesResultFlag, helperMaterializesResult,
    emptyExtractContext,
    riscv2zisk_context.Riscv2ZiskContext.store_op_typed,
    riscv2zisk_context.Riscv2ZiskContext.store_op_with_reg_offset,
    src_b_imm_zero_ok_true,
    zisk_inst_builder.ZiskInstBuilder.new_for_rv64im_lowering,
    zisk_inst_builder.ZiskInstBuilder.new,
    zisk_inst_builder.ZiskInstBuilder.Insts.CoreDefaultDefault.default,
    zisk_inst.ZiskInst.Insts.CoreDefaultDefault.default,
    zisk_inst_builder.ZiskInstBuilder.src_a_imm,
    zisk_inst_builder.ZiskInstBuilder.src_a_reg,
    zisk_inst_builder.ZiskInstBuilder.src_b_imm,
    zisk_inst_builder.ZiskInstBuilder.src_b_reg,
    zisk_inst_builder.ZiskInstBuilder.op_zisk,
    zisk_ops.ZiskOp.op_type,
    zisk_ops.ZiskOp.code,
    zisk_ops.ZiskOp.input_size,
    zisk_ops.ZiskOp.is_m32,
    zisk_inst.ZiskOperationType.Insts.CoreConvertFromOpType.from,
    zisk_inst_builder.ZiskInstBuilder.set_runtime_op_fields,
    zisk_inst_builder.ZiskInstBuilder.ind_width,
    zisk_inst_builder.ZiskInstBuilder.store_ind,
    zisk_inst_builder.ZiskInstBuilder.j,
    zisk_inst_builder.ZiskInstBuilder.build,
    riscv2zisk_context.Riscv2ZiskContext.insert_inst,
    zisk_registers.REGS_IN_MAIN_FROM,
    zisk_registers.REGS_IN_MAIN_TO,
    zisk_registers.REG_FIRST,
    mem.SYS_ADDR,
    mem.RAM_ADDR,
    u64_mk_ofNat_val,
    i64_mk_ofNat_val,
    UScalar.cast,
    UScalar.hcast,
    IScalar.cast,
    IScalar.hcast,
    lift,
    regs_from_set_width_u64_val_eq,
    regs_to_set_width_u64_val_eq,
    regs_from_set_width_i64_val_eq,
    regs_to_set_width_i64_val_eq,
    u64_add_zero_ok,
    i64_add_zero_ok,
    u64_zero_eq_zero,
    u64_zero_shift_right_32_ok,
    i64_zero_eq_zero,
    one_u64_scalar_ne_zero,
    one_i64_scalar_ne_zero,
    u64_one_val_ne_zero,
    u64_one_val_not_gt_regs_to,
    u64_31_ne_zero,
    u64_31_val_ne_zero,
    u64_31_val_not_gt_regs_to,
    i64_one_val_not_lt_regs_from,
    i64_one_val_not_gt_regs_to,
    i64_31_ne_zero,
    i64_31_val_not_lt_regs_from,
    i64_31_val_not_gt_regs_to,
    one_u64_val_not_lt_regs_from_set_width,
    regs_to_set_width_val_not_lt_one_u64,
    one_i64_val_not_lt_regs_from_set_width,
    regs_to_set_width_val_not_lt_one_i64]

set_option maxHeartbeats 4000000 in
theorem all_store_width4_symbolic_imm_materializes_result_flag
    (imm : Std.I32) :
    allRvU32Regs.all
      (fun rs1 =>
        allRvU32Regs.all
          (fun rs2 =>
            helperMaterializesResultFlag
              (fun ctx =>
                riscv2zisk_context.Riscv2ZiskContext.store_op_typed
                  ctx
                  { rom_address := 0#u64, rd := 0#u32, rs1 := rs1,
                    rs2 := rs2, imm := imm }
                  zisk_ops.ZiskOp.Add 4#u64 4#u64))) = true := by
  rw [u64_4_eq_pattern]
  simp [allRvU32Regs, helperMaterializesResultFlag, helperMaterializesResult,
    emptyExtractContext,
    riscv2zisk_context.Riscv2ZiskContext.store_op_typed,
    riscv2zisk_context.Riscv2ZiskContext.store_op_with_reg_offset,
    src_b_imm_zero_ok_true,
    zisk_inst_builder.ZiskInstBuilder.new_for_rv64im_lowering,
    zisk_inst_builder.ZiskInstBuilder.new,
    zisk_inst_builder.ZiskInstBuilder.Insts.CoreDefaultDefault.default,
    zisk_inst.ZiskInst.Insts.CoreDefaultDefault.default,
    zisk_inst_builder.ZiskInstBuilder.src_a_imm,
    zisk_inst_builder.ZiskInstBuilder.src_a_reg,
    zisk_inst_builder.ZiskInstBuilder.src_b_imm,
    zisk_inst_builder.ZiskInstBuilder.src_b_reg,
    zisk_inst_builder.ZiskInstBuilder.op_zisk,
    zisk_ops.ZiskOp.op_type,
    zisk_ops.ZiskOp.code,
    zisk_ops.ZiskOp.input_size,
    zisk_ops.ZiskOp.is_m32,
    zisk_inst.ZiskOperationType.Insts.CoreConvertFromOpType.from,
    zisk_inst_builder.ZiskInstBuilder.set_runtime_op_fields,
    zisk_inst_builder.ZiskInstBuilder.ind_width,
    zisk_inst_builder.ZiskInstBuilder.store_ind,
    zisk_inst_builder.ZiskInstBuilder.j,
    zisk_inst_builder.ZiskInstBuilder.build,
    riscv2zisk_context.Riscv2ZiskContext.insert_inst,
    zisk_registers.REGS_IN_MAIN_FROM,
    zisk_registers.REGS_IN_MAIN_TO,
    zisk_registers.REG_FIRST,
    mem.SYS_ADDR,
    mem.RAM_ADDR,
    u64_mk_ofNat_val,
    i64_mk_ofNat_val,
    UScalar.cast,
    UScalar.hcast,
    IScalar.cast,
    IScalar.hcast,
    lift,
    regs_from_set_width_u64_val_eq,
    regs_to_set_width_u64_val_eq,
    regs_from_set_width_i64_val_eq,
    regs_to_set_width_i64_val_eq,
    u64_add_zero_ok,
    i64_add_zero_ok,
    u64_zero_eq_zero,
    u64_zero_shift_right_32_ok,
    i64_zero_eq_zero,
    one_u64_scalar_ne_zero,
    one_i64_scalar_ne_zero,
    u64_one_val_ne_zero,
    u64_one_val_not_gt_regs_to,
    u64_31_ne_zero,
    u64_31_val_ne_zero,
    u64_31_val_not_gt_regs_to,
    i64_one_val_not_lt_regs_from,
    i64_one_val_not_gt_regs_to,
    i64_31_ne_zero,
    i64_31_val_not_lt_regs_from,
    i64_31_val_not_gt_regs_to,
    one_u64_val_not_lt_regs_from_set_width,
    regs_to_set_width_val_not_lt_one_u64,
    one_i64_val_not_lt_regs_from_set_width,
    regs_to_set_width_val_not_lt_one_i64]

set_option maxHeartbeats 4000000 in
theorem all_store_width8_symbolic_imm_materializes_result_flag
    (imm : Std.I32) :
    allRvU32Regs.all
      (fun rs1 =>
        allRvU32Regs.all
          (fun rs2 =>
            helperMaterializesResultFlag
              (fun ctx =>
                riscv2zisk_context.Riscv2ZiskContext.store_op_typed
                  ctx
                  { rom_address := 0#u64, rd := 0#u32, rs1 := rs1,
                    rs2 := rs2, imm := imm }
                  zisk_ops.ZiskOp.Add 8#u64 4#u64))) = true := by
  rw [u64_8_eq_pattern]
  simp [allRvU32Regs, helperMaterializesResultFlag, helperMaterializesResult,
    emptyExtractContext,
    riscv2zisk_context.Riscv2ZiskContext.store_op_typed,
    riscv2zisk_context.Riscv2ZiskContext.store_op_with_reg_offset,
    src_b_imm_zero_ok_true,
    zisk_inst_builder.ZiskInstBuilder.new_for_rv64im_lowering,
    zisk_inst_builder.ZiskInstBuilder.new,
    zisk_inst_builder.ZiskInstBuilder.Insts.CoreDefaultDefault.default,
    zisk_inst.ZiskInst.Insts.CoreDefaultDefault.default,
    zisk_inst_builder.ZiskInstBuilder.src_a_imm,
    zisk_inst_builder.ZiskInstBuilder.src_a_reg,
    zisk_inst_builder.ZiskInstBuilder.src_b_imm,
    zisk_inst_builder.ZiskInstBuilder.src_b_reg,
    zisk_inst_builder.ZiskInstBuilder.op_zisk,
    zisk_ops.ZiskOp.op_type,
    zisk_ops.ZiskOp.code,
    zisk_ops.ZiskOp.input_size,
    zisk_ops.ZiskOp.is_m32,
    zisk_inst.ZiskOperationType.Insts.CoreConvertFromOpType.from,
    zisk_inst_builder.ZiskInstBuilder.set_runtime_op_fields,
    zisk_inst_builder.ZiskInstBuilder.ind_width,
    zisk_inst_builder.ZiskInstBuilder.store_ind,
    zisk_inst_builder.ZiskInstBuilder.j,
    zisk_inst_builder.ZiskInstBuilder.build,
    riscv2zisk_context.Riscv2ZiskContext.insert_inst,
    zisk_registers.REGS_IN_MAIN_FROM,
    zisk_registers.REGS_IN_MAIN_TO,
    zisk_registers.REG_FIRST,
    mem.SYS_ADDR,
    mem.RAM_ADDR,
    u64_mk_ofNat_val,
    i64_mk_ofNat_val,
    UScalar.cast,
    UScalar.hcast,
    IScalar.cast,
    IScalar.hcast,
    lift,
    regs_from_set_width_u64_val_eq,
    regs_to_set_width_u64_val_eq,
    regs_from_set_width_i64_val_eq,
    regs_to_set_width_i64_val_eq,
    u64_add_zero_ok,
    i64_add_zero_ok,
    u64_zero_eq_zero,
    u64_zero_shift_right_32_ok,
    i64_zero_eq_zero,
    one_u64_scalar_ne_zero,
    one_i64_scalar_ne_zero,
    u64_one_val_ne_zero,
    u64_one_val_not_gt_regs_to,
    u64_31_ne_zero,
    u64_31_val_ne_zero,
    u64_31_val_not_gt_regs_to,
    i64_one_val_not_lt_regs_from,
    i64_one_val_not_gt_regs_to,
    i64_31_ne_zero,
    i64_31_val_not_lt_regs_from,
    i64_31_val_not_gt_regs_to,
    one_u64_val_not_lt_regs_from_set_width,
    regs_to_set_width_val_not_lt_one_u64,
    one_i64_val_not_lt_regs_from_set_width,
    regs_to_set_width_val_not_lt_one_i64]

/- Finite all-register store-helper materialization at zero immediate. These
cover every RV `rs1 × rs2` pair for each indirect memory width, complementing
the symbolic-immediate representative-register milestones below. -/
set_option maxHeartbeats 4000000 in
theorem all_store_width1_zero_imm_materializes_result_flag :
    allRvU32Regs.all
      (fun rs1 =>
        allRvU32Regs.all
          (fun rs2 =>
            helperMaterializesResultFlag
              (fun ctx =>
                riscv2zisk_context.Riscv2ZiskContext.store_op_typed
                  ctx
                  { rom_address := 0#u64, rd := 0#u32, rs1 := rs1,
                    rs2 := rs2, imm := 0#i32 }
                  zisk_ops.ZiskOp.Add 1#u64 4#u64))) = true := by
  native_decide

set_option maxHeartbeats 4000000 in
theorem all_store_width2_zero_imm_materializes_result_flag :
    allRvU32Regs.all
      (fun rs1 =>
        allRvU32Regs.all
          (fun rs2 =>
            helperMaterializesResultFlag
              (fun ctx =>
                riscv2zisk_context.Riscv2ZiskContext.store_op_typed
                  ctx
                  { rom_address := 0#u64, rd := 0#u32, rs1 := rs1,
                    rs2 := rs2, imm := 0#i32 }
                  zisk_ops.ZiskOp.Add 2#u64 4#u64))) = true := by
  native_decide

set_option maxHeartbeats 4000000 in
theorem all_store_width4_zero_imm_materializes_result_flag :
    allRvU32Regs.all
      (fun rs1 =>
        allRvU32Regs.all
          (fun rs2 =>
            helperMaterializesResultFlag
              (fun ctx =>
                riscv2zisk_context.Riscv2ZiskContext.store_op_typed
                  ctx
                  { rom_address := 0#u64, rd := 0#u32, rs1 := rs1,
                    rs2 := rs2, imm := 0#i32 }
                  zisk_ops.ZiskOp.Add 4#u64 4#u64))) = true := by
  native_decide

set_option maxHeartbeats 4000000 in
theorem all_store_width8_zero_imm_materializes_result_flag :
    allRvU32Regs.all
      (fun rs1 =>
        allRvU32Regs.all
          (fun rs2 =>
            helperMaterializesResultFlag
              (fun ctx =>
                riscv2zisk_context.Riscv2ZiskContext.store_op_typed
                  ctx
                  { rom_address := 0#u64, rd := 0#u32, rs1 := rs1,
                    rs2 := rs2, imm := 0#i32 }
                  zisk_ops.ZiskOp.Add 8#u64 4#u64))) = true := by
  native_decide

/-- Full production-helper memory milestone: all extracted load row builders
materialize for every RV destination/base-register pair and every extracted
signed immediate, across all supported indirect memory widths.

This is one layer below raw-instruction completeness: it proves the memory
helper bodies used by production lowering are total once decode/lowering has
routed to the helper. -/
def LoadHelperSymbolicImmediateRowsComplete : Prop :=
  ∀ imm : Std.I32,
    allRvU32Regs.all
      (fun rd =>
        allRvU32Regs.all
          (fun rs1 =>
            helperMaterializesResultFlag
              (fun ctx =>
                riscv2zisk_context.Riscv2ZiskContext.load_op_typed
                  ctx
                  { rom_address := 0#u64, rd := rd, rs1 := rs1,
                    rs2 := 0#u32, imm := imm }
                  zisk_ops.ZiskOp.Add 1#u64 4#u64))) = true ∧
    allRvU32Regs.all
      (fun rd =>
        allRvU32Regs.all
          (fun rs1 =>
            helperMaterializesResultFlag
              (fun ctx =>
                riscv2zisk_context.Riscv2ZiskContext.load_op_typed
                  ctx
                  { rom_address := 0#u64, rd := rd, rs1 := rs1,
                    rs2 := 0#u32, imm := imm }
                  zisk_ops.ZiskOp.Add 2#u64 4#u64))) = true ∧
    allRvU32Regs.all
      (fun rd =>
        allRvU32Regs.all
          (fun rs1 =>
            helperMaterializesResultFlag
              (fun ctx =>
                riscv2zisk_context.Riscv2ZiskContext.load_op_typed
                  ctx
                  { rom_address := 0#u64, rd := rd, rs1 := rs1,
                    rs2 := 0#u32, imm := imm }
                  zisk_ops.ZiskOp.Add 4#u64 4#u64))) = true ∧
    allRvU32Regs.all
      (fun rd =>
        allRvU32Regs.all
          (fun rs1 =>
            helperMaterializesResultFlag
              (fun ctx =>
                riscv2zisk_context.Riscv2ZiskContext.load_op_typed
                  ctx
                  { rom_address := 0#u64, rd := rd, rs1 := rs1,
                    rs2 := 0#u32, imm := imm }
                  zisk_ops.ZiskOp.Add 8#u64 4#u64))) = true

theorem load_helper_symbolic_immediate_rows_complete :
    LoadHelperSymbolicImmediateRowsComplete := by
  intro imm
  exact
    ⟨all_load_width1_symbolic_imm_materializes_result_flag imm,
      all_load_width2_symbolic_imm_materializes_result_flag imm,
      all_load_width4_symbolic_imm_materializes_result_flag imm,
      all_load_width8_symbolic_imm_materializes_result_flag imm⟩

/-- Full production-helper memory milestone: all extracted store row builders
materialize for every RV base/source-register pair and every extracted signed
immediate, across all supported indirect memory widths.

As with the load milestone, this proves the production helper body itself; the
remaining raw-completeness bridge is symbolic decode/lowering dispatch from
raw S-format words into these helpers. -/
def StoreHelperSymbolicImmediateRowsComplete : Prop :=
  ∀ imm : Std.I32,
    allRvU32Regs.all
      (fun rs1 =>
        allRvU32Regs.all
          (fun rs2 =>
            helperMaterializesResultFlag
              (fun ctx =>
                riscv2zisk_context.Riscv2ZiskContext.store_op_typed
                  ctx
                  { rom_address := 0#u64, rd := 0#u32, rs1 := rs1,
                    rs2 := rs2, imm := imm }
                  zisk_ops.ZiskOp.Add 1#u64 4#u64))) = true ∧
    allRvU32Regs.all
      (fun rs1 =>
        allRvU32Regs.all
          (fun rs2 =>
            helperMaterializesResultFlag
              (fun ctx =>
                riscv2zisk_context.Riscv2ZiskContext.store_op_typed
                  ctx
                  { rom_address := 0#u64, rd := 0#u32, rs1 := rs1,
                    rs2 := rs2, imm := imm }
                  zisk_ops.ZiskOp.Add 2#u64 4#u64))) = true ∧
    allRvU32Regs.all
      (fun rs1 =>
        allRvU32Regs.all
          (fun rs2 =>
            helperMaterializesResultFlag
              (fun ctx =>
                riscv2zisk_context.Riscv2ZiskContext.store_op_typed
                  ctx
                  { rom_address := 0#u64, rd := 0#u32, rs1 := rs1,
                    rs2 := rs2, imm := imm }
                  zisk_ops.ZiskOp.Add 4#u64 4#u64))) = true ∧
    allRvU32Regs.all
      (fun rs1 =>
        allRvU32Regs.all
          (fun rs2 =>
            helperMaterializesResultFlag
              (fun ctx =>
                riscv2zisk_context.Riscv2ZiskContext.store_op_typed
                  ctx
                  { rom_address := 0#u64, rd := 0#u32, rs1 := rs1,
                    rs2 := rs2, imm := imm }
                  zisk_ops.ZiskOp.Add 8#u64 4#u64))) = true

theorem store_helper_symbolic_immediate_rows_complete :
    StoreHelperSymbolicImmediateRowsComplete := by
  intro imm
  exact
    ⟨all_store_width1_symbolic_imm_materializes_result_flag imm,
      all_store_width2_symbolic_imm_materializes_result_flag imm,
      all_store_width4_symbolic_imm_materializes_result_flag imm,
      all_store_width8_symbolic_imm_materializes_result_flag imm⟩

def MemoryHelperSymbolicImmediateRowsComplete : Prop :=
  LoadHelperSymbolicImmediateRowsComplete ∧
  StoreHelperSymbolicImmediateRowsComplete

theorem memory_helper_symbolic_immediate_rows_complete :
    MemoryHelperSymbolicImmediateRowsComplete :=
  ⟨load_helper_symbolic_immediate_rows_complete,
    store_helper_symbolic_immediate_rows_complete⟩

/-- The extracted store helper materializes a row for symbolic immediates on
ordinary-register paths. This lifts the earlier representative checks past the
generated scalar `rs2 + reg_offset` step. -/
theorem empty_store_width1_reg1_symbolic_imm_materializes_result_flag
    (imm : Std.I32) :
    helperMaterializesResultFlag
      (fun ctx =>
        riscv2zisk_context.Riscv2ZiskContext.store_op_typed
          ctx
          { rom_address := 0#u64, rd := 0#u32, rs1 := 1#u32,
            rs2 := 1#u32, imm := imm }
          zisk_ops.ZiskOp.Add 1#u64 4#u64) = true := by
  rw [u64_1_eq_pattern]
  simp [helperMaterializesResultFlag, helperMaterializesResult, emptyExtractContext,
    riscv2zisk_context.Riscv2ZiskContext.store_op_typed,
    riscv2zisk_context.Riscv2ZiskContext.store_op_with_reg_offset,
    zisk_inst_builder.ZiskInstBuilder.new_for_rv64im_lowering,
    zisk_inst_builder.ZiskInstBuilder.new,
    zisk_inst_builder.ZiskInstBuilder.Insts.CoreDefaultDefault.default,
    zisk_inst.ZiskInst.Insts.CoreDefaultDefault.default,
    zisk_inst_builder.ZiskInstBuilder.src_a_reg,
    zisk_inst_builder.ZiskInstBuilder.src_b_reg,
    zisk_inst_builder.ZiskInstBuilder.op_zisk,
    zisk_ops.ZiskOp.op_type,
    zisk_ops.ZiskOp.code,
    zisk_ops.ZiskOp.input_size,
    zisk_ops.ZiskOp.is_m32,
    zisk_inst.ZiskOperationType.Insts.CoreConvertFromOpType.from,
    zisk_inst_builder.ZiskInstBuilder.set_runtime_op_fields,
    zisk_inst_builder.ZiskInstBuilder.ind_width,
    zisk_inst_builder.ZiskInstBuilder.store_ind,
    zisk_inst_builder.ZiskInstBuilder.j,
    zisk_inst_builder.ZiskInstBuilder.build,
    riscv2zisk_context.Riscv2ZiskContext.insert_inst,
    zisk_registers.REGS_IN_MAIN_FROM,
    zisk_registers.REGS_IN_MAIN_TO,
    zisk_registers.REG_FIRST,
    mem.SYS_ADDR,
    mem.RAM_ADDR,
    UScalar.cast,
    UScalar.hcast,
    IScalar.cast,
    u64_one_add_zero_ok,
    lift,
    one_u64_scalar_ne_zero,
    one_u64_val_not_lt_regs_from_set_width,
    regs_to_set_width_val_not_lt_one_u64]

theorem empty_store_width2_reg1_symbolic_imm_materializes_result_flag
    (imm : Std.I32) :
    helperMaterializesResultFlag
      (fun ctx =>
        riscv2zisk_context.Riscv2ZiskContext.store_op_typed
          ctx
          { rom_address := 0#u64, rd := 0#u32, rs1 := 1#u32,
            rs2 := 1#u32, imm := imm }
          zisk_ops.ZiskOp.Add 2#u64 4#u64) = true := by
  rw [u64_2_eq_pattern]
  simp [helperMaterializesResultFlag, helperMaterializesResult, emptyExtractContext,
    riscv2zisk_context.Riscv2ZiskContext.store_op_typed,
    riscv2zisk_context.Riscv2ZiskContext.store_op_with_reg_offset,
    zisk_inst_builder.ZiskInstBuilder.new_for_rv64im_lowering,
    zisk_inst_builder.ZiskInstBuilder.new,
    zisk_inst_builder.ZiskInstBuilder.Insts.CoreDefaultDefault.default,
    zisk_inst.ZiskInst.Insts.CoreDefaultDefault.default,
    zisk_inst_builder.ZiskInstBuilder.src_a_reg,
    zisk_inst_builder.ZiskInstBuilder.src_b_reg,
    zisk_inst_builder.ZiskInstBuilder.op_zisk,
    zisk_ops.ZiskOp.op_type,
    zisk_ops.ZiskOp.code,
    zisk_ops.ZiskOp.input_size,
    zisk_ops.ZiskOp.is_m32,
    zisk_inst.ZiskOperationType.Insts.CoreConvertFromOpType.from,
    zisk_inst_builder.ZiskInstBuilder.set_runtime_op_fields,
    zisk_inst_builder.ZiskInstBuilder.ind_width,
    zisk_inst_builder.ZiskInstBuilder.store_ind,
    zisk_inst_builder.ZiskInstBuilder.j,
    zisk_inst_builder.ZiskInstBuilder.build,
    riscv2zisk_context.Riscv2ZiskContext.insert_inst,
    zisk_registers.REGS_IN_MAIN_FROM,
    zisk_registers.REGS_IN_MAIN_TO,
    zisk_registers.REG_FIRST,
    mem.SYS_ADDR,
    mem.RAM_ADDR,
    UScalar.cast,
    UScalar.hcast,
    IScalar.cast,
    u64_one_add_zero_ok,
    lift,
    one_u64_scalar_ne_zero,
    one_u64_val_not_lt_regs_from_set_width,
    regs_to_set_width_val_not_lt_one_u64]

theorem empty_store_width4_reg1_symbolic_imm_materializes_result_flag
    (imm : Std.I32) :
    helperMaterializesResultFlag
      (fun ctx =>
        riscv2zisk_context.Riscv2ZiskContext.store_op_typed
          ctx
          { rom_address := 0#u64, rd := 0#u32, rs1 := 1#u32,
            rs2 := 1#u32, imm := imm }
          zisk_ops.ZiskOp.Add 4#u64 4#u64) = true := by
  rw [u64_4_eq_pattern]
  simp [helperMaterializesResultFlag, helperMaterializesResult, emptyExtractContext,
    riscv2zisk_context.Riscv2ZiskContext.store_op_typed,
    riscv2zisk_context.Riscv2ZiskContext.store_op_with_reg_offset,
    zisk_inst_builder.ZiskInstBuilder.new_for_rv64im_lowering,
    zisk_inst_builder.ZiskInstBuilder.new,
    zisk_inst_builder.ZiskInstBuilder.Insts.CoreDefaultDefault.default,
    zisk_inst.ZiskInst.Insts.CoreDefaultDefault.default,
    zisk_inst_builder.ZiskInstBuilder.src_a_reg,
    zisk_inst_builder.ZiskInstBuilder.src_b_reg,
    zisk_inst_builder.ZiskInstBuilder.op_zisk,
    zisk_ops.ZiskOp.op_type,
    zisk_ops.ZiskOp.code,
    zisk_ops.ZiskOp.input_size,
    zisk_ops.ZiskOp.is_m32,
    zisk_inst.ZiskOperationType.Insts.CoreConvertFromOpType.from,
    zisk_inst_builder.ZiskInstBuilder.set_runtime_op_fields,
    zisk_inst_builder.ZiskInstBuilder.ind_width,
    zisk_inst_builder.ZiskInstBuilder.store_ind,
    zisk_inst_builder.ZiskInstBuilder.j,
    zisk_inst_builder.ZiskInstBuilder.build,
    riscv2zisk_context.Riscv2ZiskContext.insert_inst,
    zisk_registers.REGS_IN_MAIN_FROM,
    zisk_registers.REGS_IN_MAIN_TO,
    zisk_registers.REG_FIRST,
    mem.SYS_ADDR,
    mem.RAM_ADDR,
    UScalar.cast,
    UScalar.hcast,
    IScalar.cast,
    u64_one_add_zero_ok,
    lift,
    one_u64_scalar_ne_zero,
    one_u64_val_not_lt_regs_from_set_width,
    regs_to_set_width_val_not_lt_one_u64]

theorem empty_store_width8_reg1_symbolic_imm_materializes_result_flag
    (imm : Std.I32) :
    helperMaterializesResultFlag
      (fun ctx =>
        riscv2zisk_context.Riscv2ZiskContext.store_op_typed
          ctx
          { rom_address := 0#u64, rd := 0#u32, rs1 := 1#u32,
            rs2 := 1#u32, imm := imm }
          zisk_ops.ZiskOp.Add 8#u64 4#u64) = true := by
  rw [u64_8_eq_pattern]
  simp [helperMaterializesResultFlag, helperMaterializesResult, emptyExtractContext,
    riscv2zisk_context.Riscv2ZiskContext.store_op_typed,
    riscv2zisk_context.Riscv2ZiskContext.store_op_with_reg_offset,
    zisk_inst_builder.ZiskInstBuilder.new_for_rv64im_lowering,
    zisk_inst_builder.ZiskInstBuilder.new,
    zisk_inst_builder.ZiskInstBuilder.Insts.CoreDefaultDefault.default,
    zisk_inst.ZiskInst.Insts.CoreDefaultDefault.default,
    zisk_inst_builder.ZiskInstBuilder.src_a_reg,
    zisk_inst_builder.ZiskInstBuilder.src_b_reg,
    zisk_inst_builder.ZiskInstBuilder.op_zisk,
    zisk_ops.ZiskOp.op_type,
    zisk_ops.ZiskOp.code,
    zisk_ops.ZiskOp.input_size,
    zisk_ops.ZiskOp.is_m32,
    zisk_inst.ZiskOperationType.Insts.CoreConvertFromOpType.from,
    zisk_inst_builder.ZiskInstBuilder.set_runtime_op_fields,
    zisk_inst_builder.ZiskInstBuilder.ind_width,
    zisk_inst_builder.ZiskInstBuilder.store_ind,
    zisk_inst_builder.ZiskInstBuilder.j,
    zisk_inst_builder.ZiskInstBuilder.build,
    riscv2zisk_context.Riscv2ZiskContext.insert_inst,
    zisk_registers.REGS_IN_MAIN_FROM,
    zisk_registers.REGS_IN_MAIN_TO,
    zisk_registers.REG_FIRST,
    mem.SYS_ADDR,
    mem.RAM_ADDR,
    UScalar.cast,
    UScalar.hcast,
    IScalar.cast,
    u64_one_add_zero_ok,
    lift,
    one_u64_scalar_ne_zero,
    one_u64_val_not_lt_regs_from_set_width,
    regs_to_set_width_val_not_lt_one_u64]

/-- Production precompile-helper materialization milestones for the DMA helper
branches present in the extracted conversion surface. -/
theorem empty_precompiled_dma_memcpy_reg1_materializes_result_flag :
    helperMaterializesResultFlag
      (fun ctx =>
        riscv2zisk_context.Riscv2ZiskContext.create_precompiled_op_typed
          ctx
          { rom_address := 0#u64, rd := 1#u32, rs1 := 1#u32,
            rs2 := 1#u32, imm := 0#i32 }
          zisk_ops.ZiskOp.DmaMemCpy
          1#u32
          1#u32
          4#u64) = true := by
  native_decide

theorem empty_precompiled_dma_memcmp_reg1_materializes_result_flag :
    helperMaterializesResultFlag
      (fun ctx =>
        riscv2zisk_context.Riscv2ZiskContext.create_precompiled_op_typed
          ctx
          { rom_address := 0#u64, rd := 1#u32, rs1 := 1#u32,
            rs2 := 1#u32, imm := 0#i32 }
          zisk_ops.ZiskOp.DmaMemCmp
          1#u32
          1#u32
          4#u64) = true := by
  native_decide

/-- A raw word accepted by the generated shape-grid checker is covered by the
same production-backed circuit predicate used by the RV completeness theorem.
The wide finite families in `GeneratedChecks.lean` prove their grids satisfy
this checker with `native_decide`. -/
def GeneratedShapeCaseOk (raw : Std.U32) : Prop :=
  zisk_core_generated_checks.rawShapeGridCaseOk raw = true

set_option maxHeartbeats 1000000 in
/-- ZisK-internal stage: every production-decoder-supported RV64IM opcode is
lowerable by the extracted production lowering function. -/
theorem rv_lowering_completeness :
    RvLoweringCompleteness := by
  intro raw h_supported
  simp [ZiskDecodeSupportedRaw,
    ZiskLowerableRaw, rawDecodeSupported, rawTranspileAcceptedFlag,
    aeneas_extract.extract_decode_rv64im_raw,
    aeneas_extract.extract_transpile_rv64im_accepted_raw] at h_supported ⊢
  cases h_decode : aeneas_extract.rv64im_decode.decode_32_core raw <;> simp [h_decode] at h_supported ⊢
  rename_i decoded
  cases decoded
  case mk opcode format funct3 funct7 rd rs1 rs2 imm pred succ =>
  cases opcode <;>
  cases format <;>
    simp [aeneas_extract.decode_extract_from_decoded,
      aeneas_extract.rv64im_decode.DecodedRv64im.is_supported_rv64im,
      aeneas_extract.lowering_opcode,
      aeneas_extract.opcode_id,
      aeneas_extract.format_id] at h_supported ⊢

/-- ZisK-internal stage: every production-decoder-supported opcode lands in the
current 63-opcode circuit/equivalence surface. -/
theorem rv_opcode_coverage_completeness :
    RvOpcodeCoverageCompleteness := by
  intro raw h_supported
  simp [ZiskDecodeSupportedRaw, rawDecodeSupported, rawDecodeOpcodeId,
    coveredOpcodeId,
    aeneas_extract.extract_decode_rv64im_raw] at h_supported ⊢
  cases h_decode : aeneas_extract.rv64im_decode.decode_32_core raw <;> simp [h_decode] at h_supported ⊢
  rename_i decoded
  cases decoded
  case mk opcode format funct3 funct7 rd rs1 rs2 imm pred succ =>
  cases opcode <;>
  cases format <;>
    simp [aeneas_extract.decode_extract_from_decoded,
      aeneas_extract.rv64im_decode.DecodedRv64im.is_supported_rv64im,
      aeneas_extract.opcode_id,
      aeneas_extract.format_id] at h_supported ⊢

/-- RV-completeness for every Sail-executable raw instruction that is not one
of the known Sail-valid/ZisK-rejected shapes. The hypothesis is deliberately
named as an avoid-known-bugs boundary so a future ZisK decoder fix can remove
it instead of weakening this theorem. -/
theorem rv_completeness_avoiding_known_bugs
    (sailExecutableRaw : Std.U32 → Prop)
    (h_avoid_known_bugs : RvAvoidKnownBugsFor sailExecutableRaw) :
    RvCompletenessAvoidingKnownBugsFor sailExecutableRaw := by
  intro raw h_sail h_not_known_gap
  have h_supported := h_avoid_known_bugs raw h_sail h_not_known_gap
  have h_materialized : ZiskRowMaterializedRaw raw := by
    simp [KnownZiskGapRaw, KnownZiskRowMaterializationGapRaw,
      ZiskDecodeSupportedRaw, ZiskRowMaterializedRaw,
      rawTranspileMaterializedFlag] at h_not_known_gap h_supported ⊢
    exact h_not_known_gap.right h_supported
  constructor
  · exact h_supported
  · constructor
    · exact rv_lowering_completeness raw h_supported
    · constructor
      · exact h_materialized
      · exact rv_opcode_coverage_completeness raw h_supported

theorem generated_shape_case_completeness
    (raw : Std.U32) (h_case : GeneratedShapeCaseOk raw) :
    ZiskCircuitCoveredRaw raw ∧ KnownZiskGapRaw raw = false := by
  have h_parts := h_case
  simp [GeneratedShapeCaseOk, zisk_core_generated_checks.rawShapeGridCaseOk,
      zisk_core_generated_checks.rawDecodeSupported,
      zisk_core_generated_checks.rawTranspileAccepted,
      zisk_core_generated_checks.rawTranspileAcceptedFlag,
      zisk_core_generated_checks.rawTranspileMaterializedFlag,
      zisk_core_generated_checks.KnownZiskGapRaw] at h_parts
  rcases h_parts with
    ⟨h_decode, _h_transpile, h_lower, h_row, h_known_decode, h_known_row⟩
  have h_supported : ZiskDecodeSupportedRaw raw := by
    simpa [ZiskDecodeSupportedRaw, rawDecodeSupported] using h_decode
  have h_lowerable : ZiskLowerableRaw raw := by
    simpa [ZiskLowerableRaw, rawTranspileAcceptedFlag] using h_lower
  have h_materialized : ZiskRowMaterializedRaw raw := by
    simpa [ZiskRowMaterializedRaw, rawTranspileMaterializedFlag] using h_row
  have h_generated_gap : zisk_core_generated_checks.KnownZiskGapRaw raw = false := by
    simp [zisk_core_generated_checks.KnownZiskGapRaw,
      h_known_decode, h_known_row]
  have h_gap : KnownZiskGapRaw raw = false := by
    simpa [KnownZiskGapRaw, KnownZiskDecodeGapRaw,
      KnownZiskRowMaterializationGapRaw,
      rawOpcode, rawFunct3, resultU32Eq, rawDecodeSupported,
      rawTranspileMaterializedFlag,
      zisk_core_generated_checks.KnownZiskGapRaw,
      zisk_core_generated_checks.KnownZiskDecodeGapRaw,
      zisk_core_generated_checks.KnownZiskRowMaterializationGapRaw,
      zisk_core_generated_checks.rawOpcode,
      zisk_core_generated_checks.rawFunct3,
      zisk_core_generated_checks.resultU32Eq,
      zisk_core_generated_checks.rawDecodeSupported,
      zisk_core_generated_checks.rawTranspileMaterializedFlag] using h_generated_gap
  exact
    ⟨⟨h_supported, h_lowerable, h_materialized,
        rv_opcode_coverage_completeness raw h_supported⟩,
      h_gap⟩

def GeneratedCircuitCoveredCaseOk (raw : Std.U32) : Bool :=
  rawDecodeSupported (aeneas_extract.extract_decode_rv64im_raw raw) &&
  rawTranspileAcceptedFlag (aeneas_extract.extract_transpile_rv64im_accepted_raw raw) &&
  rawTranspileMaterializedFlag
    (aeneas_extract.extract_transpile_rv64im_materializes_raw raw) &&
  coveredOpcodeId
    (rawDecodeOpcodeId (aeneas_extract.extract_decode_rv64im_raw raw)) &&
  !KnownZiskGapRaw raw

def GeneratedShapeGridCircuitCompleteness : Bool :=
  zisk_core_generated_checks.rawShapeGridCases.all GeneratedCircuitCoveredCaseOk

theorem generated_shape_grid_circuit_completeness :
    GeneratedShapeGridCircuitCompleteness = true := by
  native_decide

theorem generated_shape_grid_cases_circuit_covered
    (raw : Std.U32)
    (h_mem : raw ∈ zisk_core_generated_checks.rawShapeGridCases) :
    ZiskCircuitCoveredRaw raw ∧ KnownZiskGapRaw raw = false := by
  apply generated_shape_case_completeness
  have h_all :
      zisk_core_generated_checks.rawShapeGridCases.all
        zisk_core_generated_checks.rawShapeGridCaseOk = true := by
    native_decide
  exact (List.all_eq_true.mp h_all) raw h_mem

EOF

    if [[ "$AENEAS_CHECK_RV_WIDE_SHAPES" != 0 ]]; then
      cat >> "$lean_check/RvCompleteness.lean" <<'EOF'

/-!
Wide-grid family closure.

These theorems are generated only for the optional wide shape run, because the
underlying native checks are intentionally more expensive than the default
extraction smoke test. Each theorem is separated by family so a future
production decoder/lowering/materialization regression reports the failing
surface directly instead of only failing the aggregate grid.
-/

theorem generated_r_type_register_family_case_ok :
    zisk_core_generated_checks.allRTypeRegisterShapesMaterialize = true := by
  simpa using zisk_core_generated_checks.allRTypeRegisterShapesMaterialize_ok

theorem generated_r_type_register_case_circuit_covered
    (funct7 funct3 opcode rd rs1 rs2 : Nat)
    (h_op :
      (funct7, funct3, opcode) ∈
        zisk_core_generated_checks.allRTypeOpcodeShapes)
    (h_rd : rd ∈ zisk_core_generated_checks.allRvRegs)
    (h_rs1 : rs1 ∈ zisk_core_generated_checks.allRvRegs)
    (h_rs2 : rs2 ∈ zisk_core_generated_checks.allRvRegs) :
    ZiskCircuitCoveredRaw
        (zisk_core_generated_checks.rawRType
          funct7 rs2 rs1 funct3 rd opcode) ∧
      KnownZiskGapRaw
        (zisk_core_generated_checks.rawRType
          funct7 rs2 rs1 funct3 rd opcode) = false := by
  apply generated_shape_case_completeness
  have h_all := zisk_core_generated_checks.allRTypeRegisterShapesMaterialize_ok
  simp [zisk_core_generated_checks.allRTypeRegisterShapesMaterialize,
    zisk_core_generated_checks.allRTypeRegisterShapes] at h_all
  exact h_all funct7 funct3 opcode h_op rd h_rd rs1 h_rs1 rs2 h_rs2

theorem generated_i_type_register_edge_immediate_family_case_ok :
    zisk_core_generated_checks.allITypeRegisterEdgeImmediatesMaterialize = true := by
  simpa using zisk_core_generated_checks.allITypeRegisterEdgeImmediatesMaterialize_ok

theorem generated_i_type_register_edge_immediate_case_circuit_covered
    (rd rs1 imm funct3 opcode : Nat)
    (h_rd : rd ∈ zisk_core_generated_checks.allRvRegs)
    (h_rs1 : rs1 ∈ zisk_core_generated_checks.allRvRegs)
    (h_imm : imm ∈ zisk_core_generated_checks.edgeIImmediates)
    (h_shape :
      (funct3, opcode) ∈ [
        (0, 0x67), (0, 0x13), (2, 0x13), (3, 0x13), (4, 0x13),
        (6, 0x13), (7, 0x13), (0, 0x1b), (0, 0x03), (1, 0x03),
        (2, 0x03), (3, 0x03), (4, 0x03), (5, 0x03), (6, 0x03)
      ]) :
    ZiskCircuitCoveredRaw
        (zisk_core_generated_checks.rawIType imm rs1 funct3 rd opcode) ∧
      KnownZiskGapRaw
        (zisk_core_generated_checks.rawIType imm rs1 funct3 rd opcode) = false := by
  apply generated_shape_case_completeness
  have h_all := zisk_core_generated_checks.allITypeRegisterEdgeImmediatesMaterialize_ok
  simp [zisk_core_generated_checks.allITypeRegisterEdgeImmediatesMaterialize,
    zisk_core_generated_checks.allITypeRegisterEdgeImmediates] at h_all
  have h_cases := h_all rd h_rd rs1 h_rs1 imm h_imm
  simp at h_shape
  rcases h_shape with
    h_shape | h_shape | h_shape | h_shape | h_shape |
    h_shape | h_shape | h_shape | h_shape | h_shape |
    h_shape | h_shape | h_shape | h_shape | h_shape
  · rcases h_shape with ⟨rfl, rfl⟩
    exact And.left h_cases
  · rcases h_shape with ⟨rfl, rfl⟩
    exact And.left (And.right h_cases)
  · rcases h_shape with ⟨rfl, rfl⟩
    exact And.left (And.right (And.right h_cases))
  · rcases h_shape with ⟨rfl, rfl⟩
    exact And.left (And.right (And.right (And.right h_cases)))
  · rcases h_shape with ⟨rfl, rfl⟩
    exact And.left (And.right (And.right (And.right (And.right h_cases))))
  · rcases h_shape with ⟨rfl, rfl⟩
    exact And.left (And.right (And.right (And.right (And.right (And.right h_cases)))))
  · rcases h_shape with ⟨rfl, rfl⟩
    exact And.left (And.right (And.right (And.right (And.right (And.right (And.right h_cases))))))
  · rcases h_shape with ⟨rfl, rfl⟩
    exact And.left (And.right (And.right (And.right (And.right (And.right (And.right (And.right h_cases)))))))
  · rcases h_shape with ⟨rfl, rfl⟩
    exact And.left (And.right (And.right (And.right (And.right (And.right (And.right (And.right (And.right h_cases))))))))
  · rcases h_shape with ⟨rfl, rfl⟩
    exact And.left (And.right (And.right (And.right (And.right (And.right (And.right (And.right (And.right (And.right h_cases)))))))))
  · rcases h_shape with ⟨rfl, rfl⟩
    exact And.left (And.right (And.right (And.right (And.right (And.right (And.right (And.right (And.right (And.right (And.right h_cases))))))))))
  · rcases h_shape with ⟨rfl, rfl⟩
    exact And.left (And.right (And.right (And.right (And.right (And.right (And.right (And.right (And.right (And.right (And.right (And.right h_cases)))))))))))
  · rcases h_shape with ⟨rfl, rfl⟩
    exact And.left (And.right (And.right (And.right (And.right (And.right (And.right (And.right (And.right (And.right (And.right (And.right (And.right h_cases))))))))))))
  · rcases h_shape with ⟨rfl, rfl⟩
    exact And.left (And.right (And.right (And.right (And.right (And.right (And.right (And.right (And.right (And.right (And.right (And.right (And.right (And.right h_cases)))))))))))))
  · rcases h_shape with ⟨rfl, rfl⟩
    exact And.right (And.right (And.right (And.right (And.right (And.right (And.right (And.right (And.right (And.right (And.right (And.right (And.right (And.right h_cases)))))))))))))

theorem generated_shift_register_family_case_ok :
    zisk_core_generated_checks.allShiftRegisterShapesMaterialize = true := by
  simpa using zisk_core_generated_checks.allShiftRegisterShapesMaterialize_ok

theorem generated_slli_register_case_circuit_covered
    (rd rs1 shamt : Nat)
    (h_rd : rd ∈ zisk_core_generated_checks.allRvRegs)
    (h_rs1 : rs1 ∈ zisk_core_generated_checks.allRvRegs)
    (h_shamt : shamt ∈ zisk_core_generated_checks.shift64Amounts) :
    ZiskCircuitCoveredRaw
        (zisk_core_generated_checks.rawIType shamt rs1 1 rd 0x13) ∧
      KnownZiskGapRaw
        (zisk_core_generated_checks.rawIType shamt rs1 1 rd 0x13) = false := by
  apply generated_shape_case_completeness
  have h_all := zisk_core_generated_checks.allShiftRegisterShapesMaterialize_ok
  simp [zisk_core_generated_checks.allShiftRegisterShapesMaterialize,
    zisk_core_generated_checks.allShiftRegisterShapes] at h_all
  exact And.left (And.left (h_all rd h_rd rs1 h_rs1) shamt h_shamt)

theorem generated_srli_register_case_circuit_covered
    (rd rs1 shamt : Nat)
    (h_rd : rd ∈ zisk_core_generated_checks.allRvRegs)
    (h_rs1 : rs1 ∈ zisk_core_generated_checks.allRvRegs)
    (h_shamt : shamt ∈ zisk_core_generated_checks.shift64Amounts) :
    ZiskCircuitCoveredRaw
        (zisk_core_generated_checks.rawIType shamt rs1 5 rd 0x13) ∧
      KnownZiskGapRaw
        (zisk_core_generated_checks.rawIType shamt rs1 5 rd 0x13) = false := by
  apply generated_shape_case_completeness
  have h_all := zisk_core_generated_checks.allShiftRegisterShapesMaterialize_ok
  simp [zisk_core_generated_checks.allShiftRegisterShapesMaterialize,
    zisk_core_generated_checks.allShiftRegisterShapes] at h_all
  exact And.left (And.right (And.left (h_all rd h_rd rs1 h_rs1) shamt h_shamt))

theorem generated_srai_register_case_circuit_covered
    (rd rs1 shamt : Nat)
    (h_rd : rd ∈ zisk_core_generated_checks.allRvRegs)
    (h_rs1 : rs1 ∈ zisk_core_generated_checks.allRvRegs)
    (h_shamt : shamt ∈ zisk_core_generated_checks.shift64Amounts) :
    ZiskCircuitCoveredRaw
        (zisk_core_generated_checks.rawIType (0x400 ||| shamt) rs1 5 rd 0x13) ∧
      KnownZiskGapRaw
        (zisk_core_generated_checks.rawIType (0x400 ||| shamt) rs1 5 rd 0x13) = false := by
  apply generated_shape_case_completeness
  have h_all := zisk_core_generated_checks.allShiftRegisterShapesMaterialize_ok
  simp [zisk_core_generated_checks.allShiftRegisterShapesMaterialize,
    zisk_core_generated_checks.allShiftRegisterShapes] at h_all
  exact And.right (And.right (And.left (h_all rd h_rd rs1 h_rs1) shamt h_shamt))

theorem generated_slliw_register_case_circuit_covered
    (rd rs1 shamt : Nat)
    (h_rd : rd ∈ zisk_core_generated_checks.allRvRegs)
    (h_rs1 : rs1 ∈ zisk_core_generated_checks.allRvRegs)
    (h_shamt : shamt ∈ zisk_core_generated_checks.shift32Amounts) :
    ZiskCircuitCoveredRaw
        (zisk_core_generated_checks.rawIType shamt rs1 1 rd 0x1b) ∧
      KnownZiskGapRaw
        (zisk_core_generated_checks.rawIType shamt rs1 1 rd 0x1b) = false := by
  apply generated_shape_case_completeness
  have h_all := zisk_core_generated_checks.allShiftRegisterShapesMaterialize_ok
  simp [zisk_core_generated_checks.allShiftRegisterShapesMaterialize,
    zisk_core_generated_checks.allShiftRegisterShapes] at h_all
  exact And.left (And.right (h_all rd h_rd rs1 h_rs1) shamt h_shamt)

theorem generated_srliw_register_case_circuit_covered
    (rd rs1 shamt : Nat)
    (h_rd : rd ∈ zisk_core_generated_checks.allRvRegs)
    (h_rs1 : rs1 ∈ zisk_core_generated_checks.allRvRegs)
    (h_shamt : shamt ∈ zisk_core_generated_checks.shift32Amounts) :
    ZiskCircuitCoveredRaw
        (zisk_core_generated_checks.rawIType shamt rs1 5 rd 0x1b) ∧
      KnownZiskGapRaw
        (zisk_core_generated_checks.rawIType shamt rs1 5 rd 0x1b) = false := by
  apply generated_shape_case_completeness
  have h_all := zisk_core_generated_checks.allShiftRegisterShapesMaterialize_ok
  simp [zisk_core_generated_checks.allShiftRegisterShapesMaterialize,
    zisk_core_generated_checks.allShiftRegisterShapes] at h_all
  exact And.left (And.right (And.right (h_all rd h_rd rs1 h_rs1) shamt h_shamt))

theorem generated_sraiw_register_case_circuit_covered
    (rd rs1 shamt : Nat)
    (h_rd : rd ∈ zisk_core_generated_checks.allRvRegs)
    (h_rs1 : rs1 ∈ zisk_core_generated_checks.allRvRegs)
    (h_shamt : shamt ∈ zisk_core_generated_checks.shift32Amounts) :
    ZiskCircuitCoveredRaw
        (zisk_core_generated_checks.rawIType (0x400 ||| shamt) rs1 5 rd 0x1b) ∧
      KnownZiskGapRaw
        (zisk_core_generated_checks.rawIType (0x400 ||| shamt) rs1 5 rd 0x1b) = false := by
  apply generated_shape_case_completeness
  have h_all := zisk_core_generated_checks.allShiftRegisterShapesMaterialize_ok
  simp [zisk_core_generated_checks.allShiftRegisterShapesMaterialize,
    zisk_core_generated_checks.allShiftRegisterShapes] at h_all
  exact And.right (And.right (And.right (h_all rd h_rd rs1 h_rs1) shamt h_shamt))

theorem generated_store_register_edge_immediate_family_case_ok :
    zisk_core_generated_checks.allStoreRegisterEdgeImmediatesMaterialize = true := by
  simpa using zisk_core_generated_checks.allStoreRegisterEdgeImmediatesMaterialize_ok

theorem generated_store_register_edge_immediate_case_circuit_covered
    (rs1 rs2 imm funct3 : Nat)
    (h_rs1 : rs1 ∈ zisk_core_generated_checks.allRvRegs)
    (h_rs2 : rs2 ∈ zisk_core_generated_checks.allRvRegs)
    (h_imm : imm ∈ zisk_core_generated_checks.edgeSImmediates)
    (h_funct3 : funct3 ∈ [0, 1, 2, 3]) :
    ZiskCircuitCoveredRaw
        (zisk_core_generated_checks.rawSType imm rs2 rs1 funct3) ∧
      KnownZiskGapRaw
        (zisk_core_generated_checks.rawSType imm rs2 rs1 funct3) = false := by
  apply generated_shape_case_completeness
  have h_all := zisk_core_generated_checks.allStoreRegisterEdgeImmediatesMaterialize_ok
  simp [zisk_core_generated_checks.allStoreRegisterEdgeImmediatesMaterialize,
    zisk_core_generated_checks.allStoreRegisterEdgeImmediates] at h_all
  have h_cases := h_all rs1 h_rs1 rs2 h_rs2 imm h_imm
  simp at h_funct3
  rcases h_funct3 with h_funct3 | h_funct3 | h_funct3 | h_funct3
  · subst funct3
    exact And.left h_cases
  · subst funct3
    exact And.left (And.right h_cases)
  · subst funct3
    exact And.left (And.right (And.right h_cases))
  · subst funct3
    exact And.right (And.right (And.right h_cases))

theorem generated_branch_register_edge_immediate_family_case_ok :
    zisk_core_generated_checks.allBranchRegisterEdgeImmediatesMaterialize = true := by
  simpa using zisk_core_generated_checks.allBranchRegisterEdgeImmediatesMaterialize_ok

theorem generated_branch_register_edge_immediate_case_circuit_covered
    (rs1 rs2 imm funct3 : Nat)
    (h_rs1 : rs1 ∈ zisk_core_generated_checks.allRvRegs)
    (h_rs2 : rs2 ∈ zisk_core_generated_checks.allRvRegs)
    (h_imm : imm ∈ zisk_core_generated_checks.edgeBImmediates)
    (h_funct3 : funct3 ∈ [0, 1, 4, 5, 6, 7]) :
    ZiskCircuitCoveredRaw
        (zisk_core_generated_checks.rawBType imm rs2 rs1 funct3) ∧
      KnownZiskGapRaw
        (zisk_core_generated_checks.rawBType imm rs2 rs1 funct3) = false := by
  apply generated_shape_case_completeness
  have h_all := zisk_core_generated_checks.allBranchRegisterEdgeImmediatesMaterialize_ok
  simp [zisk_core_generated_checks.allBranchRegisterEdgeImmediatesMaterialize,
    zisk_core_generated_checks.allBranchRegisterEdgeImmediates] at h_all
  have h_cases := h_all rs1 h_rs1 rs2 h_rs2 imm h_imm
  simp at h_funct3
  rcases h_funct3 with h_funct3 | h_funct3 | h_funct3 | h_funct3 | h_funct3 | h_funct3
  · subst funct3
    exact And.left h_cases
  · subst funct3
    exact And.left (And.right h_cases)
  · subst funct3
    exact And.left (And.right (And.right h_cases))
  · subst funct3
    exact And.left (And.right (And.right (And.right h_cases)))
  · subst funct3
    exact And.left (And.right (And.right (And.right (And.right h_cases))))
  · subst funct3
    exact And.right (And.right (And.right (And.right (And.right h_cases))))

theorem generated_upper_and_jump_edge_immediate_family_case_ok :
    zisk_core_generated_checks.allUpperAndJumpEdgeImmediatesMaterialize = true := by
  simpa using zisk_core_generated_checks.allUpperAndJumpEdgeImmediatesMaterialize_ok

theorem generated_upper_edge_immediate_case_circuit_covered
    (rd imm opcode : Nat)
    (h_rd : rd ∈ zisk_core_generated_checks.allRvRegs)
    (h_imm : imm ∈ zisk_core_generated_checks.edgeUImmediates)
    (h_opcode : opcode ∈ [0x37, 0x17]) :
    ZiskCircuitCoveredRaw
        (zisk_core_generated_checks.rawUType imm rd opcode) ∧
      KnownZiskGapRaw
        (zisk_core_generated_checks.rawUType imm rd opcode) = false := by
  apply generated_shape_case_completeness
  have h_all := zisk_core_generated_checks.allUpperAndJumpEdgeImmediatesMaterialize_ok
  simp [zisk_core_generated_checks.allUpperAndJumpEdgeImmediatesMaterialize,
    zisk_core_generated_checks.allUpperAndJumpEdgeImmediates] at h_all
  have h_cases := And.left (h_all rd h_rd) imm h_imm
  simp at h_opcode
  rcases h_opcode with h_opcode | h_opcode
  · subst opcode
    exact And.left h_cases
  · subst opcode
    exact And.right h_cases

theorem generated_jump_edge_immediate_case_circuit_covered
    (rd imm : Nat)
    (h_rd : rd ∈ zisk_core_generated_checks.allRvRegs)
    (h_imm : imm ∈ zisk_core_generated_checks.edgeJImmediates) :
    ZiskCircuitCoveredRaw
        (zisk_core_generated_checks.rawJType imm rd) ∧
      KnownZiskGapRaw
        (zisk_core_generated_checks.rawJType imm rd) = false := by
  apply generated_shape_case_completeness
  have h_all := zisk_core_generated_checks.allUpperAndJumpEdgeImmediatesMaterialize_ok
  simp [zisk_core_generated_checks.allUpperAndJumpEdgeImmediatesMaterialize,
    zisk_core_generated_checks.allUpperAndJumpEdgeImmediates] at h_all
  exact And.right (h_all rd h_rd) imm h_imm

theorem generated_supported_fence_pred_succ_family_case_ok :
    zisk_core_generated_checks.allFencePredSuccShapesMaterialize = true := by
  simpa using zisk_core_generated_checks.allFencePredSuccShapesMaterialize_ok

theorem generated_supported_fence_pred_succ_case_circuit_covered
    (pred succ : Nat)
    (h_pred : pred ∈ List.range 16)
    (h_succ : succ ∈ List.range 16) :
    ZiskCircuitCoveredRaw
        (zisk_core_generated_checks.rawOfNat32
          ((pred <<< 24) ||| (succ <<< 20) ||| 0x0f)) ∧
      KnownZiskGapRaw
        (zisk_core_generated_checks.rawOfNat32
          ((pred <<< 24) ||| (succ <<< 20) ||| 0x0f)) = false := by
  apply generated_shape_case_completeness
  have h_all := zisk_core_generated_checks.allFencePredSuccShapesMaterialize_ok
  simp [zisk_core_generated_checks.allFencePredSuccShapesMaterialize,
    zisk_core_generated_checks.allFencePredSuccShapes] at h_all
  exact h_all pred (List.mem_range.mp h_pred) succ (List.mem_range.mp h_succ)

theorem generated_wide_rv_shape_families_case_ok :
    zisk_core_generated_checks.allWideRvShapeFamiliesMaterialize = true := by
  simpa using zisk_core_generated_checks.allWideRvShapeFamiliesMaterialize_ok

theorem generated_exhaustive_rv_shape_families_case_ok :
    zisk_core_generated_checks.allExhaustiveRvShapeFamiliesMaterialize = true := by
  simpa using zisk_core_generated_checks.allExhaustiveRvShapeFamiliesMaterialize_ok

theorem generated_edge_rv_shape_families_case_ok :
    zisk_core_generated_checks.allEdgeRvShapeFamiliesMaterialize = true := by
  simpa using zisk_core_generated_checks.allEdgeRvShapeFamiliesMaterialize_ok

def GeneratedRTypeRegisterShape (raw : Std.U32) : Prop :=
  ∃ funct7 funct3 opcode rd rs1 rs2,
    (funct7, funct3, opcode) ∈ zisk_core_generated_checks.allRTypeOpcodeShapes ∧
    rd ∈ zisk_core_generated_checks.allRvRegs ∧
    rs1 ∈ zisk_core_generated_checks.allRvRegs ∧
    rs2 ∈ zisk_core_generated_checks.allRvRegs ∧
    raw = zisk_core_generated_checks.rawRType funct7 rs2 rs1 funct3 rd opcode

def GeneratedITypeRegisterEdgeImmediateShape (raw : Std.U32) : Prop :=
  ∃ rd rs1 imm funct3 opcode,
    rd ∈ zisk_core_generated_checks.allRvRegs ∧
    rs1 ∈ zisk_core_generated_checks.allRvRegs ∧
    imm ∈ zisk_core_generated_checks.edgeIImmediates ∧
    (funct3, opcode) ∈ [
      (0, 0x67), (0, 0x13), (2, 0x13), (3, 0x13), (4, 0x13),
      (6, 0x13), (7, 0x13), (0, 0x1b), (0, 0x03), (1, 0x03),
      (2, 0x03), (3, 0x03), (4, 0x03), (5, 0x03), (6, 0x03)
    ] ∧
    raw = zisk_core_generated_checks.rawIType imm rs1 funct3 rd opcode

def GeneratedJalrRegisterEdgeImmediateShape (raw : Std.U32) : Prop :=
  ∃ rd rs1 imm,
    rd ∈ zisk_core_generated_checks.allRvRegs ∧
    rs1 ∈ zisk_core_generated_checks.allRvRegs ∧
    imm ∈ zisk_core_generated_checks.edgeIImmediates ∧
    raw = zisk_core_generated_checks.rawIType imm rs1 0 rd 0x67

def GeneratedImmediateAluRegisterEdgeImmediateShape (raw : Std.U32) : Prop :=
  ∃ rd rs1 imm funct3 opcode,
    rd ∈ zisk_core_generated_checks.allRvRegs ∧
    rs1 ∈ zisk_core_generated_checks.allRvRegs ∧
    imm ∈ zisk_core_generated_checks.edgeIImmediates ∧
    (funct3, opcode) ∈ [
      (0, 0x13), (2, 0x13), (3, 0x13), (4, 0x13),
      (6, 0x13), (7, 0x13), (0, 0x1b)
    ] ∧
    raw = zisk_core_generated_checks.rawIType imm rs1 funct3 rd opcode

def GeneratedLoadRegisterEdgeImmediateShape (raw : Std.U32) : Prop :=
  ∃ rd rs1 imm funct3,
    rd ∈ zisk_core_generated_checks.allRvRegs ∧
    rs1 ∈ zisk_core_generated_checks.allRvRegs ∧
    imm ∈ zisk_core_generated_checks.edgeIImmediates ∧
    funct3 ∈ [0, 1, 2, 3, 4, 5, 6] ∧
    raw = zisk_core_generated_checks.rawIType imm rs1 funct3 rd 0x03

def GeneratedShiftRegisterShape (raw : Std.U32) : Prop :=
  (∃ rd rs1 shamt,
    rd ∈ zisk_core_generated_checks.allRvRegs ∧
    rs1 ∈ zisk_core_generated_checks.allRvRegs ∧
    shamt ∈ zisk_core_generated_checks.shift64Amounts ∧
    raw = zisk_core_generated_checks.rawIType shamt rs1 1 rd 0x13) ∨
  (∃ rd rs1 shamt,
    rd ∈ zisk_core_generated_checks.allRvRegs ∧
    rs1 ∈ zisk_core_generated_checks.allRvRegs ∧
    shamt ∈ zisk_core_generated_checks.shift64Amounts ∧
    raw = zisk_core_generated_checks.rawIType shamt rs1 5 rd 0x13) ∨
  (∃ rd rs1 shamt,
    rd ∈ zisk_core_generated_checks.allRvRegs ∧
    rs1 ∈ zisk_core_generated_checks.allRvRegs ∧
    shamt ∈ zisk_core_generated_checks.shift64Amounts ∧
    raw = zisk_core_generated_checks.rawIType (0x400 ||| shamt) rs1 5 rd 0x13) ∨
  (∃ rd rs1 shamt,
    rd ∈ zisk_core_generated_checks.allRvRegs ∧
    rs1 ∈ zisk_core_generated_checks.allRvRegs ∧
    shamt ∈ zisk_core_generated_checks.shift32Amounts ∧
    raw = zisk_core_generated_checks.rawIType shamt rs1 1 rd 0x1b) ∨
  (∃ rd rs1 shamt,
    rd ∈ zisk_core_generated_checks.allRvRegs ∧
    rs1 ∈ zisk_core_generated_checks.allRvRegs ∧
    shamt ∈ zisk_core_generated_checks.shift32Amounts ∧
    raw = zisk_core_generated_checks.rawIType shamt rs1 5 rd 0x1b) ∨
  (∃ rd rs1 shamt,
    rd ∈ zisk_core_generated_checks.allRvRegs ∧
    rs1 ∈ zisk_core_generated_checks.allRvRegs ∧
    shamt ∈ zisk_core_generated_checks.shift32Amounts ∧
    raw = zisk_core_generated_checks.rawIType (0x400 ||| shamt) rs1 5 rd 0x1b)

def GeneratedStoreRegisterEdgeImmediateShape (raw : Std.U32) : Prop :=
  ∃ rs1 rs2 imm funct3,
    rs1 ∈ zisk_core_generated_checks.allRvRegs ∧
    rs2 ∈ zisk_core_generated_checks.allRvRegs ∧
    imm ∈ zisk_core_generated_checks.edgeSImmediates ∧
    funct3 ∈ [0, 1, 2, 3] ∧
    raw = zisk_core_generated_checks.rawSType imm rs2 rs1 funct3

def GeneratedBranchRegisterEdgeImmediateShape (raw : Std.U32) : Prop :=
  ∃ rs1 rs2 imm funct3,
    rs1 ∈ zisk_core_generated_checks.allRvRegs ∧
    rs2 ∈ zisk_core_generated_checks.allRvRegs ∧
    imm ∈ zisk_core_generated_checks.edgeBImmediates ∧
    funct3 ∈ [0, 1, 4, 5, 6, 7] ∧
    raw = zisk_core_generated_checks.rawBType imm rs2 rs1 funct3

def GeneratedUpperAndJumpEdgeImmediateShape (raw : Std.U32) : Prop :=
  (∃ rd imm opcode,
    rd ∈ zisk_core_generated_checks.allRvRegs ∧
    imm ∈ zisk_core_generated_checks.edgeUImmediates ∧
    opcode ∈ [0x37, 0x17] ∧
    raw = zisk_core_generated_checks.rawUType imm rd opcode) ∨
  (∃ rd imm,
    rd ∈ zisk_core_generated_checks.allRvRegs ∧
    imm ∈ zisk_core_generated_checks.edgeJImmediates ∧
    raw = zisk_core_generated_checks.rawJType imm rd)

def GeneratedUpperRegisterEdgeImmediateShape (raw : Std.U32) : Prop :=
  ∃ rd imm opcode,
    rd ∈ zisk_core_generated_checks.allRvRegs ∧
    imm ∈ zisk_core_generated_checks.edgeUImmediates ∧
    opcode ∈ [0x37, 0x17] ∧
    raw = zisk_core_generated_checks.rawUType imm rd opcode

def GeneratedJumpRegisterEdgeImmediateShape (raw : Std.U32) : Prop :=
  ∃ rd imm,
    rd ∈ zisk_core_generated_checks.allRvRegs ∧
    imm ∈ zisk_core_generated_checks.edgeJImmediates ∧
    raw = zisk_core_generated_checks.rawJType imm rd

def GeneratedSupportedFencePredSuccShape (raw : Std.U32) : Prop :=
  ∃ pred succ,
    pred ∈ List.range 16 ∧ succ ∈ List.range 16 ∧
    raw = zisk_core_generated_checks.rawOfNat32
      ((pred <<< 24) ||| (succ <<< 20) ||| 0x0f)

def GeneratedExhaustiveCheckedShape (raw : Std.U32) : Prop :=
  GeneratedRTypeRegisterShape raw ∨
  GeneratedShiftRegisterShape raw ∨
  GeneratedSupportedFencePredSuccShape raw

def GeneratedEdgeCheckedShape (raw : Std.U32) : Prop :=
  GeneratedITypeRegisterEdgeImmediateShape raw ∨
  GeneratedStoreRegisterEdgeImmediateShape raw ∨
  GeneratedBranchRegisterEdgeImmediateShape raw ∨
  GeneratedUpperAndJumpEdgeImmediateShape raw

def GeneratedRefinedEdgeCheckedShape (raw : Std.U32) : Prop :=
  GeneratedJalrRegisterEdgeImmediateShape raw ∨
  GeneratedImmediateAluRegisterEdgeImmediateShape raw ∨
  GeneratedLoadRegisterEdgeImmediateShape raw ∨
  GeneratedStoreRegisterEdgeImmediateShape raw ∨
  GeneratedBranchRegisterEdgeImmediateShape raw ∨
  GeneratedUpperRegisterEdgeImmediateShape raw ∨
  GeneratedJumpRegisterEdgeImmediateShape raw

def GeneratedWideCheckedShape (raw : Std.U32) : Prop :=
  GeneratedExhaustiveCheckedShape raw ∨ GeneratedEdgeCheckedShape raw

def GeneratedWideRefinedCheckedShape (raw : Std.U32) : Prop :=
  GeneratedExhaustiveCheckedShape raw ∨ GeneratedRefinedEdgeCheckedShape raw

theorem generated_r_type_register_shape_circuit_covered
    {raw : Std.U32} (h_shape : GeneratedRTypeRegisterShape raw) :
    ZiskCircuitCoveredRaw raw ∧ KnownZiskGapRaw raw = false := by
  rcases h_shape with
    ⟨funct7, funct3, opcode, rd, rs1, rs2,
      h_op, h_rd, h_rs1, h_rs2, rfl⟩
  exact generated_r_type_register_case_circuit_covered
    funct7 funct3 opcode rd rs1 rs2 h_op h_rd h_rs1 h_rs2

theorem generated_i_type_register_edge_immediate_shape_circuit_covered
    {raw : Std.U32} (h_shape : GeneratedITypeRegisterEdgeImmediateShape raw) :
    ZiskCircuitCoveredRaw raw ∧ KnownZiskGapRaw raw = false := by
  rcases h_shape with
    ⟨rd, rs1, imm, funct3, opcode,
      h_rd, h_rs1, h_imm, h_shape, rfl⟩
  exact generated_i_type_register_edge_immediate_case_circuit_covered
    rd rs1 imm funct3 opcode h_rd h_rs1 h_imm h_shape

theorem generated_jalr_register_edge_immediate_shape_circuit_covered
    {raw : Std.U32} (h_shape : GeneratedJalrRegisterEdgeImmediateShape raw) :
    ZiskCircuitCoveredRaw raw ∧ KnownZiskGapRaw raw = false := by
  rcases h_shape with
    ⟨rd, rs1, imm, h_rd, h_rs1, h_imm, rfl⟩
  exact generated_i_type_register_edge_immediate_case_circuit_covered
    rd rs1 imm 0 0x67 h_rd h_rs1 h_imm (by simp)

theorem generated_immediate_alu_register_edge_immediate_shape_circuit_covered
    {raw : Std.U32}
    (h_shape : GeneratedImmediateAluRegisterEdgeImmediateShape raw) :
    ZiskCircuitCoveredRaw raw ∧ KnownZiskGapRaw raw = false := by
  rcases h_shape with
    ⟨rd, rs1, imm, funct3, opcode,
      h_rd, h_rs1, h_imm, h_op, rfl⟩
  exact generated_i_type_register_edge_immediate_case_circuit_covered
    rd rs1 imm funct3 opcode h_rd h_rs1 h_imm
      (by
        simp at h_op ⊢
        rcases h_op with
          h_op | h_op | h_op | h_op | h_op | h_op | h_op <;>
          rcases h_op with ⟨rfl, rfl⟩ <;>
          simp)

theorem generated_load_register_edge_immediate_shape_circuit_covered
    {raw : Std.U32} (h_shape : GeneratedLoadRegisterEdgeImmediateShape raw) :
    ZiskCircuitCoveredRaw raw ∧ KnownZiskGapRaw raw = false := by
  rcases h_shape with
    ⟨rd, rs1, imm, funct3, h_rd, h_rs1, h_imm, h_funct3, rfl⟩
  apply generated_i_type_register_edge_immediate_case_circuit_covered
    rd rs1 imm funct3 0x03 h_rd h_rs1 h_imm
  simp at h_funct3 ⊢
  rcases h_funct3 with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp

theorem generated_shift_register_shape_circuit_covered
    {raw : Std.U32} (h_shape : GeneratedShiftRegisterShape raw) :
    ZiskCircuitCoveredRaw raw ∧ KnownZiskGapRaw raw = false := by
  rcases h_shape with h_shape | h_shape | h_shape | h_shape | h_shape | h_shape
  · rcases h_shape with ⟨rd, rs1, shamt, h_rd, h_rs1, h_shamt, rfl⟩
    exact generated_slli_register_case_circuit_covered rd rs1 shamt h_rd h_rs1 h_shamt
  · rcases h_shape with ⟨rd, rs1, shamt, h_rd, h_rs1, h_shamt, rfl⟩
    exact generated_srli_register_case_circuit_covered rd rs1 shamt h_rd h_rs1 h_shamt
  · rcases h_shape with ⟨rd, rs1, shamt, h_rd, h_rs1, h_shamt, rfl⟩
    exact generated_srai_register_case_circuit_covered rd rs1 shamt h_rd h_rs1 h_shamt
  · rcases h_shape with ⟨rd, rs1, shamt, h_rd, h_rs1, h_shamt, rfl⟩
    exact generated_slliw_register_case_circuit_covered rd rs1 shamt h_rd h_rs1 h_shamt
  · rcases h_shape with ⟨rd, rs1, shamt, h_rd, h_rs1, h_shamt, rfl⟩
    exact generated_srliw_register_case_circuit_covered rd rs1 shamt h_rd h_rs1 h_shamt
  · rcases h_shape with ⟨rd, rs1, shamt, h_rd, h_rs1, h_shamt, rfl⟩
    exact generated_sraiw_register_case_circuit_covered rd rs1 shamt h_rd h_rs1 h_shamt

theorem generated_store_register_edge_immediate_shape_circuit_covered
    {raw : Std.U32} (h_shape : GeneratedStoreRegisterEdgeImmediateShape raw) :
    ZiskCircuitCoveredRaw raw ∧ KnownZiskGapRaw raw = false := by
  rcases h_shape with ⟨rs1, rs2, imm, funct3,
    h_rs1, h_rs2, h_imm, h_funct3, rfl⟩
  exact generated_store_register_edge_immediate_case_circuit_covered
    rs1 rs2 imm funct3 h_rs1 h_rs2 h_imm h_funct3

theorem generated_branch_register_edge_immediate_shape_circuit_covered
    {raw : Std.U32} (h_shape : GeneratedBranchRegisterEdgeImmediateShape raw) :
    ZiskCircuitCoveredRaw raw ∧ KnownZiskGapRaw raw = false := by
  rcases h_shape with ⟨rs1, rs2, imm, funct3,
    h_rs1, h_rs2, h_imm, h_funct3, rfl⟩
  exact generated_branch_register_edge_immediate_case_circuit_covered
    rs1 rs2 imm funct3 h_rs1 h_rs2 h_imm h_funct3

theorem generated_upper_and_jump_edge_immediate_shape_circuit_covered
    {raw : Std.U32} (h_shape : GeneratedUpperAndJumpEdgeImmediateShape raw) :
    ZiskCircuitCoveredRaw raw ∧ KnownZiskGapRaw raw = false := by
  rcases h_shape with h_upper | h_jump
  · rcases h_upper with ⟨rd, imm, opcode, h_rd, h_imm, h_opcode, rfl⟩
    exact generated_upper_edge_immediate_case_circuit_covered
      rd imm opcode h_rd h_imm h_opcode
  · rcases h_jump with ⟨rd, imm, h_rd, h_imm, rfl⟩
    exact generated_jump_edge_immediate_case_circuit_covered rd imm h_rd h_imm

theorem generated_upper_register_edge_immediate_shape_circuit_covered
    {raw : Std.U32} (h_shape : GeneratedUpperRegisterEdgeImmediateShape raw) :
    ZiskCircuitCoveredRaw raw ∧ KnownZiskGapRaw raw = false := by
  rcases h_shape with ⟨rd, imm, opcode, h_rd, h_imm, h_opcode, rfl⟩
  exact generated_upper_edge_immediate_case_circuit_covered
    rd imm opcode h_rd h_imm h_opcode

theorem generated_jump_register_edge_immediate_shape_circuit_covered
    {raw : Std.U32} (h_shape : GeneratedJumpRegisterEdgeImmediateShape raw) :
    ZiskCircuitCoveredRaw raw ∧ KnownZiskGapRaw raw = false := by
  rcases h_shape with ⟨rd, imm, h_rd, h_imm, rfl⟩
  exact generated_jump_edge_immediate_case_circuit_covered rd imm h_rd h_imm

theorem generated_supported_fence_pred_succ_shape_circuit_covered
    {raw : Std.U32} (h_shape : GeneratedSupportedFencePredSuccShape raw) :
    ZiskCircuitCoveredRaw raw ∧ KnownZiskGapRaw raw = false := by
  rcases h_shape with ⟨pred, succ, h_pred, h_succ, rfl⟩
  exact generated_supported_fence_pred_succ_case_circuit_covered
    pred succ h_pred h_succ

theorem generated_exhaustive_checked_shape_circuit_covered
    {raw : Std.U32} (h_shape : GeneratedExhaustiveCheckedShape raw) :
    ZiskCircuitCoveredRaw raw ∧ KnownZiskGapRaw raw = false := by
  rcases h_shape with h_r | h_shift | h_fence
  · exact generated_r_type_register_shape_circuit_covered h_r
  · exact generated_shift_register_shape_circuit_covered h_shift
  · exact generated_supported_fence_pred_succ_shape_circuit_covered h_fence

theorem generated_edge_checked_shape_circuit_covered
    {raw : Std.U32} (h_shape : GeneratedEdgeCheckedShape raw) :
    ZiskCircuitCoveredRaw raw ∧ KnownZiskGapRaw raw = false := by
  rcases h_shape with h_i | h_store | h_branch | h_upper_jump
  · exact generated_i_type_register_edge_immediate_shape_circuit_covered h_i
  · exact generated_store_register_edge_immediate_shape_circuit_covered h_store
  · exact generated_branch_register_edge_immediate_shape_circuit_covered h_branch
  · exact generated_upper_and_jump_edge_immediate_shape_circuit_covered h_upper_jump

theorem generated_refined_edge_checked_shape_circuit_covered
    {raw : Std.U32} (h_shape : GeneratedRefinedEdgeCheckedShape raw) :
    ZiskCircuitCoveredRaw raw ∧ KnownZiskGapRaw raw = false := by
  rcases h_shape with
    h_jalr | h_alu | h_load | h_store | h_branch | h_upper | h_jump
  · exact generated_jalr_register_edge_immediate_shape_circuit_covered h_jalr
  · exact generated_immediate_alu_register_edge_immediate_shape_circuit_covered h_alu
  · exact generated_load_register_edge_immediate_shape_circuit_covered h_load
  · exact generated_store_register_edge_immediate_shape_circuit_covered h_store
  · exact generated_branch_register_edge_immediate_shape_circuit_covered h_branch
  · exact generated_upper_register_edge_immediate_shape_circuit_covered h_upper
  · exact generated_jump_register_edge_immediate_shape_circuit_covered h_jump

theorem generated_wide_checked_shape_circuit_covered
    {raw : Std.U32} (h_shape : GeneratedWideCheckedShape raw) :
    ZiskCircuitCoveredRaw raw ∧ KnownZiskGapRaw raw = false := by
  rcases h_shape with h_exhaustive | h_edge
  · exact generated_exhaustive_checked_shape_circuit_covered h_exhaustive
  · exact generated_edge_checked_shape_circuit_covered h_edge

theorem generated_wide_refined_checked_shape_circuit_covered
    {raw : Std.U32} (h_shape : GeneratedWideRefinedCheckedShape raw) :
    ZiskCircuitCoveredRaw raw ∧ KnownZiskGapRaw raw = false := by
  rcases h_shape with h_exhaustive | h_edge
  · exact generated_exhaustive_checked_shape_circuit_covered h_exhaustive
  · exact generated_refined_edge_checked_shape_circuit_covered h_edge

def GeneratedRTypeRegisterCircuitCompleteness : Bool :=
  zisk_core_generated_checks.allRTypeRegisterShapes GeneratedCircuitCoveredCaseOk

def GeneratedITypeRegisterEdgeImmediateCircuitCompleteness : Bool :=
  zisk_core_generated_checks.allITypeRegisterEdgeImmediates GeneratedCircuitCoveredCaseOk

def GeneratedShiftRegisterCircuitCompleteness : Bool :=
  zisk_core_generated_checks.allShiftRegisterShapes GeneratedCircuitCoveredCaseOk

def GeneratedStoreRegisterEdgeImmediateCircuitCompleteness : Bool :=
  zisk_core_generated_checks.allStoreRegisterEdgeImmediates GeneratedCircuitCoveredCaseOk

def GeneratedBranchRegisterEdgeImmediateCircuitCompleteness : Bool :=
  zisk_core_generated_checks.allBranchRegisterEdgeImmediates GeneratedCircuitCoveredCaseOk

def GeneratedUpperAndJumpEdgeImmediateCircuitCompleteness : Bool :=
  zisk_core_generated_checks.allUpperAndJumpEdgeImmediates GeneratedCircuitCoveredCaseOk

def GeneratedSupportedFencePredSuccCircuitCompleteness : Bool :=
  zisk_core_generated_checks.allFencePredSuccShapes GeneratedCircuitCoveredCaseOk

def GeneratedExhaustiveRvShapeFamiliesCircuitCompleteness : Bool :=
  GeneratedRTypeRegisterCircuitCompleteness &&
  GeneratedShiftRegisterCircuitCompleteness &&
  GeneratedSupportedFencePredSuccCircuitCompleteness

def GeneratedEdgeRvShapeFamiliesCircuitCompleteness : Bool :=
  GeneratedITypeRegisterEdgeImmediateCircuitCompleteness &&
  GeneratedStoreRegisterEdgeImmediateCircuitCompleteness &&
  GeneratedBranchRegisterEdgeImmediateCircuitCompleteness &&
  GeneratedUpperAndJumpEdgeImmediateCircuitCompleteness

def GeneratedRefinedEdgeRvShapeFamiliesCircuitCompleteness : Bool :=
  GeneratedEdgeRvShapeFamiliesCircuitCompleteness

def GeneratedWideRvShapeFamiliesCircuitCompleteness : Bool :=
  GeneratedExhaustiveRvShapeFamiliesCircuitCompleteness &&
  GeneratedEdgeRvShapeFamiliesCircuitCompleteness

def GeneratedWideRefinedRvShapeFamiliesCircuitCompleteness : Bool :=
  GeneratedExhaustiveRvShapeFamiliesCircuitCompleteness &&
  GeneratedRefinedEdgeRvShapeFamiliesCircuitCompleteness

theorem generated_r_type_register_family_circuit_completeness :
    GeneratedRTypeRegisterCircuitCompleteness = true := by
  native_decide

theorem generated_i_type_register_edge_immediate_family_circuit_completeness :
    GeneratedITypeRegisterEdgeImmediateCircuitCompleteness = true := by
  native_decide

theorem generated_shift_register_family_circuit_completeness :
    GeneratedShiftRegisterCircuitCompleteness = true := by
  native_decide

theorem generated_store_register_edge_immediate_family_circuit_completeness :
    GeneratedStoreRegisterEdgeImmediateCircuitCompleteness = true := by
  native_decide

theorem generated_branch_register_edge_immediate_family_circuit_completeness :
    GeneratedBranchRegisterEdgeImmediateCircuitCompleteness = true := by
  native_decide

theorem generated_upper_and_jump_edge_immediate_family_circuit_completeness :
    GeneratedUpperAndJumpEdgeImmediateCircuitCompleteness = true := by
  native_decide

theorem generated_supported_fence_pred_succ_family_circuit_completeness :
    GeneratedSupportedFencePredSuccCircuitCompleteness = true := by
  native_decide

theorem generated_exhaustive_rv_shape_families_circuit_completeness :
    GeneratedExhaustiveRvShapeFamiliesCircuitCompleteness = true := by
  simp [GeneratedExhaustiveRvShapeFamiliesCircuitCompleteness,
    generated_r_type_register_family_circuit_completeness,
    generated_shift_register_family_circuit_completeness,
    generated_supported_fence_pred_succ_family_circuit_completeness]

theorem generated_edge_rv_shape_families_circuit_completeness :
    GeneratedEdgeRvShapeFamiliesCircuitCompleteness = true := by
  simp [GeneratedEdgeRvShapeFamiliesCircuitCompleteness,
    generated_i_type_register_edge_immediate_family_circuit_completeness,
    generated_store_register_edge_immediate_family_circuit_completeness,
    generated_branch_register_edge_immediate_family_circuit_completeness,
    generated_upper_and_jump_edge_immediate_family_circuit_completeness]

theorem generated_refined_edge_rv_shape_families_circuit_completeness :
    GeneratedRefinedEdgeRvShapeFamiliesCircuitCompleteness = true := by
  simpa [GeneratedRefinedEdgeRvShapeFamiliesCircuitCompleteness]
    using generated_edge_rv_shape_families_circuit_completeness

theorem generated_wide_rv_shape_families_circuit_completeness :
    GeneratedWideRvShapeFamiliesCircuitCompleteness = true := by
  simp [GeneratedWideRvShapeFamiliesCircuitCompleteness,
    generated_exhaustive_rv_shape_families_circuit_completeness,
    generated_edge_rv_shape_families_circuit_completeness]

theorem generated_wide_refined_rv_shape_families_circuit_completeness :
    GeneratedWideRefinedRvShapeFamiliesCircuitCompleteness = true := by
  simp [GeneratedWideRefinedRvShapeFamiliesCircuitCompleteness,
    generated_exhaustive_rv_shape_families_circuit_completeness,
    generated_refined_edge_rv_shape_families_circuit_completeness]

EOF
    fi

    cat >> "$lean_check/RvCompleteness.lean" <<'EOF'

-- Remaining ZisK-internal strengthening target. This asks whether every
-- lowerable decoded opcode emits a row through production lowering. A direct
-- proof by unfolding all row-builder branches currently times out after
-- several minutes, so it needs helper-total row-builder lemmas rather than
-- one monolithic `simp`.
--
-- Closed helper milestones:
-- * symbolic ordinary-register helpers for NOP, ADDI/immediate wrapper, HINT,
--   register ADD, branch EQ/NE, COPYB from rs1/rs2, LUI, AUIPC, and JAL;
-- * representative boolean totality checks for aligned/unaligned JALR,
--   load/store widths 1/2/4/8, and the DMA precompile helpers;
-- * scalar-pattern normalization for the extracted `ind_width` width branch
--   used by load/store helpers;
-- * ordinary register-1/register-2 routing totality for extracted
--   `src_a_reg`, `src_b_reg`, and `store_reg`;
-- * all-register finite routing totality for extracted `src_a_reg`,
--   `src_b_reg`, and `store_reg`;
-- * wide generated raw-shape families covering all registers for R-type and
--   shifts, all supported FENCE pred/succ shapes, and edge immediates for
--   I/S/B/U/J-shaped instructions.
--
-- The remaining gap is the universal lift from representative/helper checks
-- to `RvRowMaterializationCompleteness` for every lowerable raw instruction.
-- The current blocker is Lean normalization of Aeneas-generated scalar code,
-- especially all-register routing comparisons after `BitVec.setWidth`.
--
-- The next useful decomposition is:
--
-- * lift the finite routing facts into symbolic helper-total theorems for
--   load/store/JALR and the remaining row builders;
-- * discharge the remaining finite register/opcode splits.
--
-- theorem rv_row_materialization_completeness :
--     RvRowMaterializationCompleteness := by
--   intro raw h_lowerable
--   exact ?row_builder_total_for_all_lowerable_shapes

example :
    rawTranspileAccepted (aeneas_extract.extract_transpile_rv64im_raw 0x00b50533#u32) = true := by
  native_decide

example :
    coveredOpcodeId
      (rawDecodeOpcodeId (aeneas_extract.extract_decode_rv64im_raw 0x00b50533#u32)) = true := by
  native_decide

example :
    rawDecodeSupported (aeneas_extract.extract_decode_rv64im_raw 0x1000000F#u32) = false := by
  native_decide

example :
    KnownZiskDecodeGapRaw 0x1000000F#u32 = true := by
  native_decide

example :
    KnownZiskGapRaw 0x1000000F#u32 = true := by
  native_decide

example :
    KnownZiskDecodeGapRaw 0x0000000F#u32 = false := by
  native_decide

example :
    KnownZiskRowMaterializationGapRaw 0x0000000F#u32 = false := by
  native_decide

example :
    KnownZiskGapRaw 0x0000000F#u32 = false := by
  native_decide

example :
    KnownZiskDecodeGapRaw 0x0000800F#u32 = true := by
  native_decide

example :
    KnownZiskDecodeGapRaw 0x0000008F#u32 = true := by
  native_decide

example :
    KnownZiskDecodeGapRaw 0x00000013#u32 = false := by
  native_decide

example :
    KnownZiskDecodeGapRaw 0x8330000F#u32 = true := by
  native_decide

-- Main target. Keep this stated here as the RV-completeness goal. It is not
-- proved in this Aeneas-only module: generic FENCE encodings currently supply
-- real counterexamples where Sail decodes but the extracted production ZisK
-- decoder rejects.
--
-- theorem rv_completeness
--     (sailExecutableRaw : Std.U32 → Prop)
--     (h_no_known_bugs : ∀ raw, sailExecutableRaw raw → ZiskDecodeSupportedRaw raw)
--     RvCompletenessFor sailExecutableRaw := by
--   intro raw h_sail
--   have h_not_known_gap : KnownZiskGapRaw raw = false := by
--     exact ?no_known_gap_for_full_completeness
--   exact rv_completeness_avoiding_known_bugs sailExecutableRaw
--     (fun raw h_sail _ => h_no_known_bugs raw h_sail)
--     raw h_sail h_not_known_gap

end zisk_core_generated_rv_completeness
EOF
    nix develop "$ROOT" --command bash -lc 'cd "$1" && lake build ProductionM2 GeneratedChecks RvCompleteness' bash "$lean_check"
  elif [[ "$AENEAS_CHECK_RV64IM_COMPLETENESS" != 0 ]]; then
    cat > "$lean_check/Rv64imCompleteness.lean" <<'EOF'
import ProductionM2

open Aeneas Aeneas.Std Result
open zisk_core

namespace zisk_core_generated_rv64im_completeness

def rawDecodeSupported (result : Result aeneas_extract.Rv64imDecodeExtract) : Bool :=
  match result with
  | ok decoded => decoded.supported
  | fail _ => false
  | div => false

def rawTranspileAccepted (result : Result aeneas_extract.Rv64imTranspileExtract) : Bool :=
  match result with
  | ok summary => summary.accepted
  | fail _ => false
  | div => false

def rawTranspileAcceptedFlag (result : Result Bool) : Bool :=
  match result with
  | ok accepted => accepted
  | fail _ => false
  | div => false

def rawTranspileRowBOffset (result : Result aeneas_extract.Rv64imTranspileExtract) : Nat :=
  match result with
  | ok summary => summary.row.b_offset_imm0.val
  | fail _ => 0
  | div => 0

def rv64imOpcode (raw : Std.U32) (opcode : Std.U32) : Result Bool := do
  let masked ← lift (raw &&& 0x7F#u32)
  ok (masked = opcode)

def rawFunct3 (raw : Std.U32) : Result Std.U32 := do
  let masked ← lift (raw &&& 0x7000#u32)
  masked >>> 12#i32

def rawFunct7 (raw : Std.U32) : Result Std.U32 := do
  let masked ← lift (raw &&& 0xFE000000#u32)
  masked >>> 25#i32

def SailAddEncoding (raw : Std.U32) : Prop :=
  rv64imOpcode raw 0x33#u32 = ok true ∧
  rawFunct3 raw = ok 0#u32 ∧
  rawFunct7 raw = ok 0#u32

def ExtractedRawRv64imCompletenessFor (sailExecutable : Std.U32 → Prop) : Prop :=
  ∀ raw, sailExecutable raw →
    rawTranspileAccepted (aeneas_extract.extract_transpile_rv64im_raw raw) = true

def ExtractedRawAddCompleteness : Prop :=
  ExtractedRawRv64imCompletenessFor SailAddEncoding

def ExtractedDecodeSupportedCompleteness : Prop :=
  ∀ raw,
    rawDecodeSupported (aeneas_extract.extract_decode_rv64im_raw raw) = true →
    rawTranspileAccepted (aeneas_extract.extract_transpile_rv64im_raw raw) = true

def ExtractedDecodeSupportedLowerableCompleteness : Prop :=
  ∀ raw,
    rawDecodeSupported (aeneas_extract.extract_decode_rv64im_raw raw) = true →
    rawTranspileAcceptedFlag (aeneas_extract.extract_transpile_rv64im_accepted_raw raw) = true

theorem extracted_decode_supported_lowerable_completeness :
    ExtractedDecodeSupportedLowerableCompleteness := by
  intro raw h_supported
  simp [rawDecodeSupported, rawTranspileAcceptedFlag,
    aeneas_extract.extract_decode_rv64im_raw,
    aeneas_extract.extract_transpile_rv64im_accepted_raw] at h_supported ⊢
  cases h_decode : aeneas_extract.rv64im_decode.decode_32_core raw <;> simp [h_decode] at h_supported ⊢
  rename_i decoded
  cases decoded
  case mk opcode format funct3 funct7 rd rs1 rs2 imm pred succ =>
  cases opcode <;>
  cases format <;>
    simp [aeneas_extract.decode_extract_from_decoded,
      aeneas_extract.rv64im_decode.DecodedRv64im.is_supported_rv64im,
      aeneas_extract.lowering_opcode,
      aeneas_extract.opcode_id,
      aeneas_extract.format_id] at h_supported ⊢

example :
    rawDecodeSupported (aeneas_extract.extract_decode_rv64im_raw 0x00b50533#u32) = true := by
  native_decide

example :
    rawTranspileAccepted (aeneas_extract.extract_transpile_rv64im_raw 0x00b50533#u32) = true := by
  native_decide

example :
    rawTranspileRowBOffset (aeneas_extract.extract_transpile_rv64im_raw 0x00b50533#u32) = 11 := by
  native_decide

example :
    rawDecodeSupported (aeneas_extract.extract_decode_rv64im_raw 0x1000000F#u32) = false := by
  native_decide

example :
    rawTranspileAccepted (aeneas_extract.extract_transpile_rv64im_raw 0x1000000F#u32) = false := by
  native_decide

end zisk_core_generated_rv64im_completeness
EOF
    nix develop "$ROOT" --command bash -lc 'cd "$1" && lake build ProductionM2 GeneratedChecks Rv64imCompleteness' bash "$lean_check"
  else
    nix develop "$ROOT" --command bash -lc 'cd "$1" && lake build ProductionM2 GeneratedChecks' bash "$lean_check"
  fi
fi

echo "Production-backed extraction succeeded: ${#starts[@]} starts, $decl_count declarations, $generated"
