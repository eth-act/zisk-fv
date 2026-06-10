{ stdenv, lib, pil-extract, zisk-pilout, zisk-src }:

# Run `pil-extract` over `zisk-pilout` (and `zisk-src` for the
# arith-table data / original PIL source) to produce the generated extraction
# circuit shim, per-AIR Lean files, the operation-bus `Buses.lean`, the
# memory-bus `MemoryBuses.lean`, the 74-row `ArithTable.lean` lookup data, the
# Mem AIR sidecar source report, and the typed Mem generated-artifact wrapper.
# All output lands in $out/.

stdenv.mkDerivation {
  pname = "zisk-fv-extracted-lean";
  version = "1.0";
  dontUnpack = true;

  buildPhase = ''
    runHook preBuild
    mkdir -p $out

    # Generated-only circuit interface consumed by the old per-AIR extraction
    # files. It is namespaced under `Extraction` so it does not collide with
    # Clean's root `Circuit` monad when generated modules are compiled together
    # with the maintained FV library.
    ${pil-extract}/bin/pil-extract circuit-shim \
      --output $out/Circuit.lean

    # Full-AIR extractions (with --skip-unsupported for the
    # FixedCol/Challenge operands the V1 extractor doesn't render).
    for air in Mem MemAlign MemAlignByte MemAlignReadByte MemAlignWriteByte \
               Binary BinaryExtension BinaryAdd; do
      ${pil-extract}/bin/pil-extract air \
        --pilout ${zisk-pilout} \
        --air "$air" \
        --skip-unsupported \
        --output "$out/$air.lean"
    done

    # Subset extractions for Main and Arith. Indices match
    # `Airs/Main.lean::extraction_bridge`; they shifted from the
    # v0.15.0 set (8,9,15,16,17,18,19,20,24,30) when ZisK reorganised
    # operation-bus emissions in v0.16.0+.
    ${pil-extract}/bin/pil-extract air --pilout ${zisk-pilout} --air Main \
      --only 7,8,13,14,15,16,17,18,22,28 \
      --output $out/Main.lean

    ${pil-extract}/bin/pil-extract air --pilout ${zisk-pilout} --air Arith \
      --only 2,6,7,8,31,32,33,34,35,36,37,38,40,41,42,43,44,45,46 \
      --output $out/Arith.lean

    # Bus-emission extraction for the operation bus (id=5000) across
    # the 5 AIRs that emit on it.
    ${pil-extract}/bin/pil-extract bus-emissions --pilout ${zisk-pilout} \
      --airs Main,Arith,Binary,BinaryAdd,BinaryExtension \
      --bus-id 5000 \
      --output $out/Buses.lean

    # Memory-bus emissions (id=10) for Main + the 4 MemAlign* provider
    # AIRs. Main's reads-side `proves` halves emit non-zero multiplicity;
    # assumes-side mirrors are stubbed where they reference ExtF challenge
    # cells that the V1 renderer does not lift (see `hint_uses_extf` gate
    # in tools/pil-extract/src/main.rs). The MemAlign* AIRs supply the
    # provider tuples for sub-doubleword loads (LBU/LHU/LWU); their bus
    # emissions feed `Airs/MemoryBus/MemAlignBridge.lean`'s perm-soundness
    # axiom.
    ${pil-extract}/bin/pil-extract bus-emissions --pilout ${zisk-pilout} \
      --airs Main,MemAlign,MemAlignByte,MemAlignReadByte,MemAlignWriteByte \
      --bus-id 10 \
      --output $out/MemoryBuses.lean

    # Arith state-machine lookup table (74 rows). Parsed straight from
    # the upstream Rust source; the constant is itself emitted by PIL
    # with `generate_table = 1`.
    ${pil-extract}/bin/pil-extract arith-table \
      --rust-source ${zisk-src}/state-machines/arith/src/arith_table_data.rs \
      --output $out/ArithTable.lean

    # Mem generated AIR facts and sidecar source map. This is not a Lake
    # dependency; it is the reproducible source manifest for the generated
    # `FullWitnessMemAirSourceRawSidecars` proof/artifact path.
    ${pil-extract}/bin/pil-extract mem-air-facts \
      --pilout ${zisk-pilout} \
      --air Mem \
      --pil-source ${zisk-src}/state-machines/mem/pil/mem.pil \
      --output $out/MemAirFacts.md

    # Typed Lean wrapper for the generated Mem artifact. The wrapper is not
    # a proof of the sidecar facts; it pins the generated module's public
    # entry point to the current load-facing timeline constructor.
    ${pil-extract}/bin/pil-extract mem-generated-artifact \
      --pilout ${zisk-pilout} \
      --air Mem \
      --output $out/MemGeneratedArtifact.lean

    runHook postBuild
  '';

  dontInstall = true;

  meta = with lib; {
    description = "Per-AIR Lean files plus Mem sidecar artifacts extracted from zisk-pilout";
    license = with licenses; [ asl20 mit ];
  };
}
