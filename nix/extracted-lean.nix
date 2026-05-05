{ stdenv, lib, pil-extract, zisk-pilout }:

# Run `pil-extract` over `zisk-pilout` to produce per-AIR Lean files.
# Mirrors the steps in the old docker/build-zisk-lean.sh: full-AIR
# extractions for memory + binary AIRs, --only filters for Main and
# Arith (proofs only need a subset), and bus-emission extraction for
# the operation bus across the AIRs that emit on it.
#
# Output: $out/<AIR>.lean files. The two hand-written extraction files
# (`ArithTable.lean`, `MemoryBuses.lean`, `OperationBuses.lean`) stay
# tracked in the repo and are NOT regenerated here — apps.populate
# only refreshes the auto-extracted set.

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
      ${pil-extract}/bin/pil-extract \
        --pilout ${zisk-pilout} \
        --air "$air" \
        --skip-unsupported \
        --output "$out/$air.lean"
    done

    # Subset extractions for Main and Arith. Indices match
    # `Airs/Main.lean::extraction_bridge`; they shifted from the
    # v0.15.0 set (8,9,15,16,17,18,19,20,24,30) when ZisK reorganised
    # operation-bus emissions in v0.16.0+.
    ${pil-extract}/bin/pil-extract --pilout ${zisk-pilout} --air Main \
      --only 7,8,13,14,15,16,17,18,22,28 \
      --output $out/Main.lean

    ${pil-extract}/bin/pil-extract --pilout ${zisk-pilout} --air Arith \
      --only 2,6,7,8,31,32,33,34,35,36,37,38,40,41,42,43,44,45,46 \
      --output $out/Arith.lean

    # Bus-emission extraction for the operation bus (id=5000) across
    # the 5 AIRs that emit on it.
    ${pil-extract}/bin/pil-extract --pilout ${zisk-pilout} \
      --airs Main,Arith,Binary,BinaryAdd,BinaryExtension \
      --bus-emissions --bus-id 5000 \
      --output $out/Buses.lean

    runHook postBuild
  '';

  dontInstall = true;

  meta = with lib; {
    description = "Per-AIR Lean files extracted from zisk-pilout";
    license = with licenses; [ asl20 mit ];
  };
}
