#!/usr/bin/env bash
set -euo pipefail

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
WORKSPACE="$ROOT/build/aeneas-production-extraction"
AENEAS_CHECK_LEAN="${AENEAS_CHECK_LEAN:-1}"

if [[ -z "${AENEAS_FLAKE:-}" ]]; then
  aeneas_owner="$(jq -r '.nodes.aeneas.locked.owner' "$ROOT/flake.lock")"
  aeneas_repo="$(jq -r '.nodes.aeneas.locked.repo' "$ROOT/flake.lock")"
  aeneas_rev="$(jq -r '.nodes.aeneas.locked.rev' "$ROOT/flake.lock")"
  AENEAS_FLAKE="github:$aeneas_owner/$aeneas_repo/$aeneas_rev"
fi

mkdir -p "$WORKSPACE"
rm -rf "$WORKSPACE/Lean" "$WORKSPACE/lean-check"
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

starts=(
  crate::aeneas_extract::extract_lui_from_inst
  crate::aeneas_extract::extract_auipc_from_inst
  crate::aeneas_extract::extract_jal_from_inst
  crate::aeneas_extract::extract_jalr_from_inst
  crate::aeneas_extract::extract_fence_from_inst
  crate::aeneas_extract::extract_add_from_inst
  crate::aeneas_extract::extract_sub_from_inst
  crate::aeneas_extract::extract_sll_from_inst
  crate::aeneas_extract::extract_slt_from_inst
  crate::aeneas_extract::extract_sltu_from_inst
  crate::aeneas_extract::extract_xor_from_inst
  crate::aeneas_extract::extract_srl_from_inst
  crate::aeneas_extract::extract_sra_from_inst
  crate::aeneas_extract::extract_or_from_inst
  crate::aeneas_extract::extract_and_from_inst
  crate::aeneas_extract::extract_addw_from_inst
  crate::aeneas_extract::extract_subw_from_inst
  crate::aeneas_extract::extract_sllw_from_inst
  crate::aeneas_extract::extract_srlw_from_inst
  crate::aeneas_extract::extract_sraw_from_inst
  crate::aeneas_extract::extract_mul_from_inst
  crate::aeneas_extract::extract_mulh_from_inst
  crate::aeneas_extract::extract_mulhsu_from_inst
  crate::aeneas_extract::extract_mulhu_from_inst
  crate::aeneas_extract::extract_mulw_from_inst
  crate::aeneas_extract::extract_div_from_inst
  crate::aeneas_extract::extract_divu_from_inst
  crate::aeneas_extract::extract_divw_from_inst
  crate::aeneas_extract::extract_divuw_from_inst
  crate::aeneas_extract::extract_rem_from_inst
  crate::aeneas_extract::extract_remu_from_inst
  crate::aeneas_extract::extract_remw_from_inst
  crate::aeneas_extract::extract_remuw_from_inst
  crate::aeneas_extract::extract_addi_from_inst
  crate::aeneas_extract::extract_slli_from_inst
  crate::aeneas_extract::extract_slti_from_inst
  crate::aeneas_extract::extract_sltiu_from_inst
  crate::aeneas_extract::extract_xori_from_inst
  crate::aeneas_extract::extract_srli_from_inst
  crate::aeneas_extract::extract_srai_from_inst
  crate::aeneas_extract::extract_ori_from_inst
  crate::aeneas_extract::extract_andi_from_inst
  crate::aeneas_extract::extract_addiw_from_inst
  crate::aeneas_extract::extract_slliw_from_inst
  crate::aeneas_extract::extract_srliw_from_inst
  crate::aeneas_extract::extract_sraiw_from_inst
  crate::aeneas_extract::extract_beq_from_inst
  crate::aeneas_extract::extract_bne_from_inst
  crate::aeneas_extract::extract_blt_from_inst
  crate::aeneas_extract::extract_bge_from_inst
  crate::aeneas_extract::extract_bltu_from_inst
  crate::aeneas_extract::extract_bgeu_from_inst
  crate::aeneas_extract::extract_lb_from_inst
  crate::aeneas_extract::extract_lbu_from_inst
  crate::aeneas_extract::extract_lh_from_inst
  crate::aeneas_extract::extract_lhu_from_inst
  crate::aeneas_extract::extract_lw_from_inst
  crate::aeneas_extract::extract_lwu_from_inst
  crate::aeneas_extract::extract_ld_from_inst
  crate::aeneas_extract::extract_sb_from_inst
  crate::aeneas_extract::extract_sh_from_inst
  crate::aeneas_extract::extract_sw_from_inst
  crate::aeneas_extract::extract_sd_from_inst
)

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
  if ! grep -q "def aeneas_extract\\.$fn" "$generated"; then
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
  cp -R "$AENEAS_LEAN_SRC" "$lean_check/aeneas-lean"
  chmod -R u+w "$lean_check/aeneas-lean"

  cat > "$lean_check/lakefile.lean" <<'EOF'
import Lake
open Lake DSL

require aeneas from "aeneas-lean"

package zisk_production_extraction_check

@[default_target] lean_lib ProductionM2
@[default_target] lean_lib GeneratedChecks
EOF
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

example :
    rowModeMatches (aeneas_extract.extract_lui_from_inst sampleInst)
      1 false false false 2 2 3 4 4 = true := by
  native_decide

example :
    rowModeMatches (aeneas_extract.extract_auipc_from_inst sampleInst)
      0 false false true 2 2 3 4 4096 = true := by
  native_decide

example :
    rowModeMatches (aeneas_extract.extract_jal_from_inst sampleInst)
      0 false false true 2 2 3 4096 4 = true := by
  native_decide

example :
    rowModeMatches (aeneas_extract.extract_addw_from_inst sampleInst)
      26 true true false 6 6 3 4 4 = true := by
  native_decide

end zisk_core_generated_checks
EOF

  nix develop "$ROOT" --command bash -lc 'cd "$1" && lake build ProductionM2 GeneratedChecks' bash "$lean_check"
fi

echo "Production-backed extraction succeeded: ${#starts[@]} starts, $decl_count declarations, $generated"
