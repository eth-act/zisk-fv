#!/usr/bin/env bash
set -euo pipefail

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
WORKSPACE="$ROOT/build/aeneas-production-extraction"
AENEAS_FLAKE="${AENEAS_FLAKE:-github:AeneasVerif/aeneas}"

mkdir -p "$WORKSPACE"
rm -rf "$WORKSPACE/Lean"
rm -f "$WORKSPACE/production_m2.llbc"

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

if grep -En '(^axiom|^opaque|sorry|unknown definitions|HashMap|alloc\.string|alloc\.fmt|Str\.|core\.fmt)' "$generated"; then
  echo "Production extraction generated an unexpected trust marker" >&2
  exit 1
fi

echo "Production-backed extraction succeeded: $decl_count declarations, $generated"
