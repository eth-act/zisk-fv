#!/usr/bin/env bash
set -euo pipefail

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
WORKSPACE="$ROOT/tools/aeneas-rv64im-extraction"
AENEAS_FLAKE="${AENEAS_FLAKE:-github:AeneasVerif/aeneas}"
LEAN_TOOLCHAIN="leanprover/lean4:v4.28.0"
EXPECTED_VALID_CASES=71
EXPECTED_INVALID_CASES=3

patch_aeneas_runtime_for_lean428() {
  printf '%s\n' "$LEAN_TOOLCHAIN" > "$WORKSPACE/lean-toolchain"
  printf '%s\n' "$LEAN_TOOLCHAIN" > "$WORKSPACE/.aeneas-lean/lean-toolchain"
  rm -rf "$WORKSPACE/.lake" "$WORKSPACE/.aeneas-lean/.lake"
  rm -f "$WORKSPACE/lake-manifest.json" "$WORKSPACE/.aeneas-lean/lake-manifest.json"

  perl -0pi -e 's/v4\.30\.0-rc2/v4.28.0/g' "$WORKSPACE/.aeneas-lean/lakefile.lean"
  perl -0pi -e '$old = q{(@Monoid.toPow _
          (@MonoidWithZero.toMonoid _
            (@Semiring.toMonoidWithZero _
              (@CommSemiring.toSemiring _ (@CommRing.toCommSemiring _ (ZMod.commRing _))))))};
    $new = q{(@Monoid.toNatPow _
          (@MonoidWithZero.toMonoid _
            (@Semiring.toMonoidWithZero _
              (@CommSemiring.toSemiring _ (@CommRing.toCommSemiring _ (ZMod.commRing _))))))};
    s/\Q$old\E/$new/ or die "failed to patch Aeneas ReduceZMod power instance\n"' \
      "$WORKSPACE/.aeneas-lean/Aeneas/Tactic/Simproc/ReduceZMod/ReduceZMod.lean"
  perl -ni -e 'print unless /^@\[implicit_reducible\]\s*$/' \
    "$WORKSPACE/.aeneas-lean/Aeneas/Std/Scalar/Core.lean"
  perl -0pi -e 's/wp x := \{\n    trans Q := match x with \| \.ok a => Q\.1 a \| \.fail e => Q\.2\.1 e \| \.div => Q\.2\.2\.1 \(\)\n    conjunctiveRaw Q₁ Q₂ := by\n      apply SPred\.bientails\.of_eq\n      cases x <;> simp\n  \}/wp x := {\n    apply := fun Q => match x with | .ok a => Q.1 a | .fail e => Q.2.1 e | .div => Q.2.2.1 ()\n    conjunctive := by\n      intro Q₁ Q₂\n      apply SPred.bientails.of_eq\n      cases x <;> simp\n  }/' \
    "$WORKSPACE/.aeneas-lean/Aeneas/Std/WP.lean"
  perl -0pi -e 's/wp_pure a := by apply PredTrans\.ext; intro Q; simp \[PredTrans\.apply, wp, WP\.wp\]; rfl/wp_pure a := by ext Q; simp [PredTrans.apply, wp, WP.wp]/; s/wp_bind x f := by apply PredTrans\.ext; intro Q; simp \[PredTrans\.apply, wp, WP\.wp\]; cases x <;> rfl/wp_bind x f := by ext Q; simp [PredTrans.apply, wp, WP.wp]; cases x <;> rfl/' \
    "$WORKSPACE/.aeneas-lean/Aeneas/Std/WP.lean"
}

patch_generated_for_lean428() {
  perl -0pi -e 's/import Aeneas\n/import Aeneas.Std.Primitives\nimport Aeneas.Std.Array\nimport Aeneas.Std.Core.Default\nimport Aeneas.Std.Scalar\n/' \
    "$WORKSPACE/Rv64imExtract/Generated.lean"
  perl -ni -e 'print unless /^@\[discriminant isize\]\s*$/' \
    "$WORKSPACE/Rv64imExtract/Generated.lean"
}

count_prefixed_theorems() {
  local file="$1"
  local prefix="$2"
  grep -Ec "^theorem ${prefix}" "$file"
}

check_manifest_coverage() {
  local generated_cases="$WORKSPACE/Rv64imExtract/GeneratedCases.lean"
  local main_cases="$WORKSPACE/MainModelCases.lean"
  local cross_cases="$WORKSPACE/Rv64imExtract/CrossModelCases.lean"

  local aeneas_count
  local invalid_count
  local main_count
  local cross_count
  aeneas_count="$(count_prefixed_theorems "$generated_cases" "decode_lower_")"
  invalid_count="$(grep -Ec '^theorem decode_lower_invalid_' "$generated_cases")"
  main_count="$(count_prefixed_theorems "$main_cases" "transpile_")"
  cross_count="$(count_prefixed_theorems "$cross_cases" "aeneas_eq_main_static_")"

  if [[ "$aeneas_count" -ne $((EXPECTED_VALID_CASES + EXPECTED_INVALID_CASES)) ]]; then
    echo "Aeneas case theorem count drifted: got $aeneas_count, expected $((EXPECTED_VALID_CASES + EXPECTED_INVALID_CASES))" >&2
    exit 1
  fi
  if [[ "$invalid_count" -ne "$EXPECTED_INVALID_CASES" ]]; then
    echo "Aeneas invalid-case theorem count drifted: got $invalid_count, expected $EXPECTED_INVALID_CASES" >&2
    exit 1
  fi
  if [[ "$main_count" -ne "$EXPECTED_VALID_CASES" ]]; then
    echo "Main static case theorem count drifted: got $main_count, expected $EXPECTED_VALID_CASES" >&2
    exit 1
  fi
  if [[ "$cross_count" -ne "$EXPECTED_VALID_CASES" ]]; then
    echo "Cross-model equality theorem count drifted: got $cross_count, expected $EXPECTED_VALID_CASES" >&2
    exit 1
  fi
}

echo "Resolving Aeneas source from $AENEAS_FLAKE"
AENEAS_SRC="$(nix flake metadata --json "$AENEAS_FLAKE" | jq -r '.path')"
if [[ -z "$AENEAS_SRC" || "$AENEAS_SRC" == "null" ]]; then
  echo "Could not resolve Aeneas source path" >&2
  exit 1
fi

if [[ -d "$WORKSPACE/.aeneas-lean" ]]; then
  chmod -R u+w "$WORKSPACE/.aeneas-lean"
fi
rm -rf "$WORKSPACE/.aeneas-lean"
cp -R "$AENEAS_SRC/backends/lean" "$WORKSPACE/.aeneas-lean"
chmod -R u+w "$WORKSPACE/.aeneas-lean"
patch_aeneas_runtime_for_lean428

rm -f "$WORKSPACE/rv64im_transpiler.llbc"
rm -f "$WORKSPACE/Rv64imExtract/Generated.lean"
rm -f "$WORKSPACE/Rv64imExtract/GeneratedCases.lean"
rm -f "$WORKSPACE/Rv64imExtract/CrossModelCases.lean"
rm -f "$WORKSPACE/MainModelCases.lean"

(
  cd "$ROOT/zisk/core"
  nix run "$AENEAS_FLAKE#charon" -- cargo --preset=aeneas \
    --start-from crate::rv64im_transpiler::decode_rv64im32 \
    --start-from crate::rv64im_transpiler::lower_rv64im32 \
    --start-from crate::rv64im_transpiler::decode_and_lower_rv64im32 \
    --dest-file "$WORKSPACE/rv64im_transpiler.llbc" \
    -- --lib
)

(
  cd "$WORKSPACE"
  nix run "$AENEAS_FLAKE#aeneas" -- \
    -backend lean \
    -dest Rv64imExtract \
    rv64im_transpiler.llbc
)

mv "$WORKSPACE/Rv64imExtract/Rv64imTranspiler.lean" "$WORKSPACE/Rv64imExtract/Generated.lean"
patch_generated_for_lean428

(
  cd "$ROOT/zisk/core"
  cargo run --quiet --example aeneas_bridge_cases -- \
    "$WORKSPACE/Rv64imExtract/GeneratedCases.lean" \
    "$WORKSPACE/MainModelCases.lean" \
    "$WORKSPACE/Rv64imExtract/CrossModelCases.lean"
)

check_manifest_coverage

if grep -En '(^axiom|unknown definitions|Option\.map|^opaque)' \
  "$WORKSPACE/Rv64imExtract/Generated.lean" \
  "$WORKSPACE/Rv64imExtract/Bridge.lean" \
  "$WORKSPACE/Rv64imExtract/GeneratedCases.lean" \
  "$WORKSPACE/Rv64imExtract/CrossModelCases.lean" \
  "$WORKSPACE/MainModelCases.lean"; then
  echo "Aeneas extraction harness generated an unexpected trust marker or unknown translation" >&2
  exit 1
fi

(
  cd "$ROOT"
  lake env lean "$WORKSPACE/MainModelCases.lean"
)

(
  cd "$WORKSPACE"
  elan run "$LEAN_TOOLCHAIN" lake update
  elan run "$LEAN_TOOLCHAIN" lake build Rv64imExtract
)
