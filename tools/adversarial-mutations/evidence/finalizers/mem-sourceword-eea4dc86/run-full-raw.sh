#!/usr/bin/env bash
set -euo pipefail
cd /home/cody/zisk-fv-closure-extractor
out=build/mem-sourceword-1ef2bc8d
observer=build/mem-c33-equation-evidence/FullRawObserver.lean
git rev-parse HEAD > "$out/checked-source-head.txt"
sha256sum "$observer" ZiskFv/AirsClean/Mem/Stage2/{Cubic,Equations,Native,PolynomialRow,Literals,Local}.lean ZiskFv/AirsClean/MemAlignWriteByte/{RawSource,SourceInstance,NativeTraceWords,SourceLiterals}.lean ZiskFv/AirsClean/Mem/{SourceFinalizerEquation,SourceFinalizer}.lean build/extraction/Extraction/{LookupWiring,Mem,Circuit}.lean > "$out/checked-inputs.sha256"
for suffix in SourceFinalizer Stage2.Cubic Stage2.Equations Stage2.Native Stage2.PolynomialRow Stage2.Literals Stage2.Local; do
  { time lake env lean -j2 --run "$observer" "ZiskFv.AirsClean.Mem.$suffix" "$out/full-raw/$suffix"; } > "$out/$suffix-full-raw.log" 2>&1
done
jq -s '{modules:., total_roots:(map(.root_count)|add), raw_axiom_union:(map(.raw_axiom_union)|add|unique)}' "$out"/full-raw/*/summary.json > "$out/full-raw-summary.json"
jq -e '.raw_axiom_union == ["Classical.choice","Quot.sound","propext"] and (.modules|length)==7 and all(.modules[]; .root_count>0)' "$out/full-raw-summary.json"
