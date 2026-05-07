{ stdenv, lib, pil-extract, zisk-pilout, zisk-src }:

# Run `pil-extract` over `zisk-pilout` (and `zisk-src` for the
# arith-table data) to produce per-AIR Lean files plus the operation-bus
# `Buses.lean`, the memory-bus `MemoryBuses.lean`, and the 74-row
# `ArithTable.lean` lookup data. All output lands in $out/.

stdenv.mkDerivation {
  pname = "zisk-fv-extracted-lean";
  version = "1.0";
  dontUnpack = true;

  buildPhase = ''
    runHook preBuild
    mkdir -p $out

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

    # Memory-bus emissions (id=10) for AIR Main. The 3 reads-side
    # `proves` halves emit non-zero multiplicity; assumes-side mirrors
    # are stubbed (they reference ExtF challenge cells that the V1
    # renderer does not lift — see `tools/pil-extract/src/main.rs`'s
    # `hint_uses_extf` gate).
    ${pil-extract}/bin/pil-extract bus-emissions --pilout ${zisk-pilout} \
      --airs Main \
      --bus-id 10 \
      --output $out/MemoryBuses.lean

    # Arith state-machine lookup table (74 rows). Parsed straight from
    # the upstream Rust source; the constant is itself emitted by PIL
    # with `generate_table = 1`.
    ${pil-extract}/bin/pil-extract arith-table \
      --rust-source ${zisk-src}/state-machines/arith/src/arith_table_data.rs \
      --output $out/ArithTable.lean

    runHook postBuild
  '';

  dontInstall = true;

  meta = with lib; {
    description = "Per-AIR Lean files extracted from zisk-pilout";
    license = with licenses; [ asl20 mit ];
  };
}
