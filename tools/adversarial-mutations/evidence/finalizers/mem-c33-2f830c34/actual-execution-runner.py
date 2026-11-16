from pathlib import Path
import subprocess, json, hashlib, os, time, shutil, sys
ROOT=Path('/home/cody/zisk-fv-closure-extractor')
CASE=Path('/tmp/mem-c33-real-source-controls.pk6x1Z')
INPUT=ROOT/'build/zisk.pilout'
CLI=CASE/'bin/pil-extract'
MUT=CASE/'bin/mem-c33-pilout-mutate'
PROBE=CASE/'MemC33SourceFidelity.lean'
INPUT_SHA='e816e4fd728fae4b0b55cac6da01312adf72afe152fe22a47da7610cf0338e6f'
CASES=['baseline','neutral_clone','group_to_air0','group_index1','direct_sign','drop_direct5','l1_rotation0']
ENV={**os.environ,'LEAN_NUM_THREADS':'2','CARGO_BUILD_JOBS':'2'}
def digest(p): return hashlib.sha256(p.read_bytes()).hexdigest()
assert digest(INPUT)==INPUT_SHA
probe_sha=digest(PROBE)
results_path=CASE/'campaign-results.json'
results=json.loads(results_path.read_text()) if results_path.exists() else {'scope':'actual compiled-source fidelity only','sourceHead':'19f0ba22e238dc87b226e99c0040cf5a36841ef1','independentEquationBaseline':'dc7cc4d6d692cf1067af769b1abb84158af0f73f','inputSHA256':INPUT_SHA,'cliSHA256':digest(CLI),'mutatorSHA256':digest(MUT),'immutableProbeSHA256':probe_sha,'proofTarget':'MemC33SourceFidelity.mem_c33_actual_compiled_source_fidelity','cases':{}}
def save(): results_path.write_text(json.dumps(results,indent=2)+'\n')
def execute(case,name,command):
 rec=results['cases'][case]
 old=rec['steps'].get(name)
 if old and old['exit']==0: return old
 history=rec.setdefault('failedAttempts',{}).setdefault(name,[])
 if old: history.append(old)
 log=CASE/case/(name+(('-attempt'+str(len(history)+1)) if history else '')+'.log')
 started=time.monotonic()
 with log.open('w') as stream:
  code=subprocess.run([str(x) for x in command],cwd=ROOT,env=ENV,stdout=stream,stderr=subprocess.STDOUT).returncode
 record={'command':[str(x) for x in command],'exit':code,'wallSeconds':round(time.monotonic()-started,3),'log':str(log)}
 rec['steps'][name]=record;save()
 return record
for case in CASES:
 path=CASE/case
 path.mkdir(exist_ok=True)
 (path/'Extraction').mkdir(exist_ok=True)
 (path/'olean/Extraction').mkdir(parents=True,exist_ok=True)
 rec=results['cases'].setdefault(case,{'steps':{},'status':'not_run'})
 if rec['status'] in ['GREEN_control','REJECTED_named_source_fidelity']: continue
 assert digest(PROBE)==probe_sha
 shutil.copyfile(PROBE,path/'MemC33SourceFidelity.lean')
 stages=[
 ('source_mutation',[MUT,'--input',INPUT,'--output',path/'input.pilout','--case',case,'--report',path/'source-change.json']),
 ('normal_circuit_producer',[CLI,'circuit-shim','--output',path/'Extraction/Circuit.lean']),
 ('normal_lookup_producer',[CLI,'lookup-wiring','--pilout',path/'input.pilout','--output',path/'Extraction/LookupWiring.lean']),
 ('normal_full_mem_producer',[CLI,'air','--pilout',path/'input.pilout','--air','Mem','--output',path/'Extraction/Mem.lean'])]
 for name,command in stages:
  step=execute(case,name,command)
  if step['exit']:
   rec['status']='SETUP_OR_PRODUCER_FAILURE_NOT_KILL';save();print(case,name,'FAILED; NOT A KILL');sys.exit(1)
 rec['sourceSHA256']=digest(path/'input.pilout')
 rec['lookupSHA256']=digest(path/'Extraction/LookupWiring.lean')
 rec['memSHA256']=digest(path/'Extraction/Mem.lean')
 rec['mutation']=json.loads((path/'source-change.json').read_text())
 for module in ['Circuit','LookupWiring','Mem']:
  script='export LEAN_PATH="$1/olean:$LEAN_PATH"; exec lean -j2 -R "$1" -o "$1/olean/Extraction/'+module+'.olean" "$1/Extraction/'+module+'.lean"'
  step=execute(case,'generated_'+module,['lake','env','bash','-c',script,'_',path])
  if step['exit']:
   rec['status']='GENERATED_MODULE_FAILURE_NOT_KILL';save();print(case,module,'FAILED; NOT A KILL');sys.exit(1)
 step=execute(case,'named_source_fidelity',['lake','env','bash','-c','export LEAN_PATH="$1/olean:$LEAN_PATH"; exec lean -j2 -R "$1" "$1/MemC33SourceFidelity.lean"','_',path])
 if case in ['baseline','neutral_clone']:
  if step['exit']:
   rec['status']='CONTROL_FAILURE_NOT_KILL';save();print(case,'CONTROL FAILED');sys.exit(1)
  rec['status']='GREEN_control'
 else:
  text=Path(step['log']).read_text()
  forbidden=['unknown identifier','unknown constant','failed to import','object file','maximum recursion depth','maximum number of heartbeats','PANIC','unexpected token']
  named_refl_failure=step['exit']!=0 and ('Tactic `rfl` failed' in text or "tactic 'rfl' failed" in text or 'unsolved goals' in text)
  if not named_refl_failure or any(bad.lower() in text.lower() for bad in forbidden):
   rec['status']='UNEXPECTED_PROBE_OUTCOME_NOT_KILL';save();print(case,'UNCLASSIFIED PROBE OUTCOME; NOT A KILL');sys.exit(1)
  assert results['cases']['baseline']['status']=='GREEN_control' and results['cases']['neutral_clone']['status']=='GREEN_control'
  rec['status']='REJECTED_named_source_fidelity'
  rec['killLayer']='kernel-checked source fidelity of real compiled PilOut input, not native execution or numeric logUp'
 save();print(case,rec['status'],flush=True)
results['status']='GREEN_baseline_and_neutral_5_valid_source_mutants_rejected'
results['noNixNoNode']=True
results['noGeneratedLeanMutation']=True
results['noNativeAuthOrLiveMemClosureClaim']=True
save()
print(results['status'])
