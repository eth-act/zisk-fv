{ writeShellApplication, nodejs_20, coreutils, pil2-compiler, pil2-proofman-src, fixed-data }:

# Same compiler and actual external columns as zisk-pilout. Only the copied PIL
# source is variable; Rust fixed-generator mutations require fresh fixed data.
writeShellApplication {
  name = "compile-mutation";
  runtimeInputs = [ nodejs_20 coreutils ];
  text = ''
    if [ "$#" -ne 2 ]; then
      echo "usage: compile-mutation ISOLATED_SOURCE OUTPUT_PILOUT" >&2
      exit 2
    fi
    mutation_source=$(realpath "$1")
    mutation_output=$(realpath -m "$2")
    test -f "$mutation_source/pil/zisk.pil"
    for payload in \
      state-machines/arith/src/arith_frops_fixed.bin \
      state-machines/binary/src/binary_basic_frops_fixed.bin \
      state-machines/binary/src/binary_extension_frops_fixed.bin; do
      mkdir -p "$mutation_source/$(dirname "$payload")"
      cp --no-preserve=mode "${fixed-data}/$payload" "$mutation_source/$payload"
    done
    cd "$mutation_source"
    exec node --max-old-space-size=16384 \
      ${pil2-compiler}/src/pil.js pil/zisk.pil \
      -I pil,${pil2-proofman-src}/pil2-components/lib/std/pil,state-machines,precompiles \
      -i "$mutation_source" -o "$mutation_output" -O fixed-to-file
  '';
}
