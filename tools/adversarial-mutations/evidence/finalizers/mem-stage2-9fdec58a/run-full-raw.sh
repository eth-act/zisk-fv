#!/usr/bin/env bash
set -euo pipefail
cd /home/cody/zisk-fv-closure-extractor
out=build/mem-stage2-687cbb47
observer=build/mem-c33-equation-evidence/FullRawObserver.lean
git rev-parse HEAD > "$out/checked-source-head.txt"
sha256sum "$observer" ZiskFv/AirsClean/Mem/Stage2/{Cubic,Equations,Native,PolynomialRow,Literals,Local}.lean ZiskFv/AirsClean/MemAlignWriteByte/{RawSource,SourceInstance,SourceLiterals}.lean ZiskFv/AirsClean/Mem/{SourceFinalizerEquation,SourceFinalizer}.lean build/extraction/Extraction/{LookupWiring,Mem,Circuit}.lean > "$out/checked-inputs.sha256"
for name in Cubic Equations Native PolynomialRow Literals Local; do
  { time lake env lean -j2 --run "$observer" "ZiskFv.AirsClean.Mem.Stage2.$name" "$out/full-raw/$name"; } > "$out/$name-full-raw.log" 2>&1
done
jq -s '{modules:., total_roots:(map(.root_count)|add), raw_axiom_union:(map(.raw_axiom_union)|add|unique)}' "$out"/full-raw/*/summary.json > "$out/full-raw-summary.json"
jq -e '.raw_axiom_union == ["Classical.choice","Quot.sound","propext"] and (.modules|length)==6 and all(.modules[]; .root_count>0)' "$out/full-raw-summary.json"
