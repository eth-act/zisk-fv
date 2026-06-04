#!/usr/bin/env bash
set -euo pipefail

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
WORKSPACE="$ROOT/build/aeneas-production-extraction"
AENEAS_CHECK_LEAN="${AENEAS_CHECK_LEAN:-1}"
AENEAS_CHECK_FENCE_COMPLETENESS="${AENEAS_CHECK_FENCE_COMPLETENESS:-0}"
AENEAS_CHECK_RV64IM_COMPLETENESS="${AENEAS_CHECK_RV64IM_COMPLETENESS:-0}"

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
  "$WORKSPACE/lean-check/Rv64imCompleteness.lean"
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
EOF_CASE
    done
  } >> "$lean_check/GeneratedChecks.lean"

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
