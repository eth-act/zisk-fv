#!/usr/bin/env python3
import json, os, re, html
import os
SP = os.environ.get("SWEEP_ROOT", os.path.dirname(os.path.abspath(__file__)))
REPO="/home/cody/zisk-fv"
R=f"{SP}/rounds"

def read(p,d=""):
    try: return open(p).read()
    except OSError: return d
def e(s): return html.escape(str(s))

CLOSURE=set()
def closure(root="ZiskFv.Soundness"):
    seen,stack=set(),[root]
    while stack:
        m=stack.pop()
        if m in seen: continue
        seen.add(m)
        for base in (REPO, os.path.join(REPO,"build/extraction")):
            f=os.path.join(base,m.replace(".","/")+".lean")
            if os.path.exists(f):
                stack+=[i for i in re.findall(r"^import ([\w.]+)",open(f).read(),re.M)
                        if i.startswith(("ZiskFv","Extraction"))]
                break
    return seen
CLOSURE=closure()

rounds=[]
for n in sorted((x for x in os.listdir(R) if x.isdigit()), key=int):
    d=f"{R}/{n}"
    if not os.path.exists(f"{d}/site.json"): continue
    s=json.load(open(f"{d}/site.json"))
    sem=None
    if os.path.exists(f"{d}/semdiff.json"):
        sem=json.load(open(f"{d}/semdiff.json"))
    changed=[os.path.basename(l.split()[1]) for l in read(f"{d}/extraction.changed").splitlines()
             if l.startswith("Files ")]
    errs=read(f"{d}/errors.txt")
    mods=sorted({m for m in re.findall(r"error: (ZiskFv/\S+?\.lean):",errs)})
    rounds.append(dict(n=int(n),site=s,status=read(f"{d}/status","?").strip(),
        invalid=bool(read(f"{d}/status.invalid").strip()),
        changed=sorted(set(changed)), exit=read(f"{d}/build.exit").strip(),
        time=read(f"{d}/build.time").strip(), rt=read(f"{d}/roundtrip.exit").strip(),
        errs=[re.sub(r"^\d+:","",x) for x in errs.strip().splitlines()][:3],
        mods=[m.replace("/",".")[:-5] for m in mods],
        note=read(f"{d}/note.md").strip(), sem=sem))

def semchanged(r):
    if not r["sem"]: return {}
    return {a:v for a,v in r["sem"]["airs"].items()
            if v.get("changed") or v.get("dropped") or v.get("added")}

def klass(r):
    s=r["site"]
    if r["invalid"]: return "nontest","site sits inside a <code>/* … */</code> block comment"
    if "witness width bits" in s["desc"]:
        return "nontest","<code>bits(n)</code> is a <code>witness_bits</code> hint, not a constraint"
    if r["status"]=="COMPILER_REJECTED": return "nontest","ZisK's own PIL compiler rejects the mutant"
    if r["status"]=="NO_EXTRACTION_DELTA": return "nontest","extracted Lean is byte-identical"
    if s["kind"]=="direct": return "valid","lookup-table data the extractor reads from ZisK source"
    ch=semchanged(r)
    if not ch: return "control","polynomial unchanged — commutativity only"
    parts=[]
    for a,v in ch.items():
        bit=f"<code>{a}</code> "
        if v["changed"]:
            c=v["changed"]
            bit += "c"+(",".join(map(str,c)) if len(c)<=4 else f"{c[0]}–{c[-1]} ({len(c)})")
        if v["dropped"]: bit += f" (dropped c{v['dropped'][0]})"
        parts.append(bit)
    return "valid","changes ZisK's compiled constraints: "+"; ".join(parts)

def verdict(r):
    k,_=klass(r)
    if k=="nontest": return "nontest","not a test"
    if k=="control": return "control","control"
    if r["exit"]=="": return "nontest","untested"
    return ("caught","caught") if r["exit"]!="0" else ("missed","missed")

for r in rounds:
    r["k"],r["why"]=klass(r); r["v"],r["vlabel"]=verdict(r)

nv=[r for r in rounds if r["k"]=="valid"]
caught=[r for r in nv if r["v"]=="caught"]; missed=[r for r in nv if r["v"]=="missed"]
ctrl=[r for r in rounds if r["k"]=="control"]; nont=[r for r in rounds if r["k"]=="nontest"]

# --- coverage table -----------------------------------------------------
import glob
AIRS=["Main","Arith","Binary","BinaryAdd","BinaryExtension","Mem","MemAlign",
      "MemAlignByte","MemAlignReadByte","MemAlignWriteByte"]
EX=f"{SP}/extraction-pristine-nix/Extraction"
emitted={a:len(set(re.findall(r"def constraint_(\d+)_every_row",read(f"{EX}/{a}.lean")))) for a in AIRS}
named={a:set() for a in AIRS}
for p in glob.glob(f"{REPO}/ZiskFv/**/*.lean",recursive=True):
    src=open(p).read()
    for a in AIRS:
        named[a].update(int(m) for m in re.findall(rf"\b{a}\.extraction\.constraint_(\d+)_every_row",src))
cov_rows="".join(
  f'<tr><td><code>{a}</code></td><td class="num">{emitted[a]}</td>'
  f'<td class="num">{len(named[a])}</td>'
  f'<td class="num"><span class="bar"><i style="width:{(100*len(named[a])//emitted[a]) if emitted[a] else 0}%"></i></span>'
  f'{(100*len(named[a])//emitted[a]) if emitted[a] else 0}%</td></tr>' for a in AIRS)
tot_e=sum(emitted.values()); tot_n=sum(len(v) for v in named.values())

# --- catcher table ------------------------------------------------------
import collections
cc=collections.Counter()
for r in rounds:
    if r["exit"] and r["exit"]!="0" and r["mods"]: cc[r["mods"][0]]+=1
catch_rows="".join(
  f'<tr><td><code>{m.replace("ZiskFv.","")}</code></td><td class="num">{k}</td>'
  f'<td>{"<b class=in>in closure</b>" if m in CLOSURE else "<span class=out>leaf audit module</span>"}</td></tr>'
  for m,k in cc.most_common())

# --- grid ---------------------------------------------------------------
grid="".join(
  f'<a class="cell {r["v"]}" href="#r{r["n"]}" title="round {r["n"]} · {e(r["site"]["air"])} · '
  f'{e(r["site"]["op"])} · {r["vlabel"]}"><span>{r["n"]}</span></a>' for r in rounds)

DISPO={}
for n in (7,16,22):  DISPO[n]=("fix","check exists, unwired")
for n in (32,38,46): DISPO[n]=("fix","needs a proves_operation template")
for n in (5,26,33,36): DISPO[n]=("bug","broken generated module")
DISPO[27]=("scope","documented out of scope")

# --- round rows ---------------------------------------------------------
def row(r):
    s=r["site"]
    mods=", ".join(f'<code>{m.replace("ZiskFv.","")}</code>' for m in r["mods"]) or "—"
    inside=any(m in CLOSURE for m in r["mods"])
    build = ("—" if not r["exit"] else
             (f'<b class="caught">fails</b>' if r["exit"]!="0" else '<b class="missed">passes</b>'))
    delta=", ".join(x[:-5] for x in r["changed"]) or "none"
    detail=""
    if r["errs"]:
        detail+='<div class="lab">Lean error</div><pre class="err">'+ "\n".join(e(x[:260]) for x in r["errs"])+"</pre>"
    if r["changed"]:
        detail+=f'<div class="lab">Generated files changed</div><p class="fine">{e(delta)}</p>'
    if r["mods"]:
        detail+=(f'<div class="lab">Failing module</div><p class="fine">{mods} — '
                 +("<b>inside</b>" if inside else "outside")
                 +" <code>root_soundness</code>’s import closure.</p>")
    if r["note"]:
        body=re.sub(r"\*\*(.+?)\*\*",r"<b>\1</b>",e(r["note"]))
        body=re.sub(r"`(.+?)`",r"<code>\1</code>",body)
        detail+='<div class="lab">Why this is a reasonable thing to break</div>'+ \
                "".join(f"<p>{p.strip()}</p>" for p in body.split("\n\n"))
    return f'''<tr id="r{r['n']}" class="v-{r['v']}">
<td class="num">{r['n']}</td>
<td><span class="tag">{e(s['air'])}</span></td>
<td><code class="op">{e(s['op'])}</code></td>
<td class="site"><code>{e(os.path.basename(s['file']))}:{s['line']}</code><br><span class="fine">{e(s['desc'])}</span></td>
<td class="why">{r['why']}</td>
<td>{build}</td>
<td><span class="pill {r['v']}">{r['vlabel']}</span>{
 f'<br><span class="dtag {DISPO[r["n"]][0]}">{DISPO[r["n"]][1]}</span>' if r['n'] in DISPO else ''
}</td>
</tr>
<tr class="det v-{r['v']}"><td></td><td colspan="6"><details><summary>round {r['n']} detail</summary>
<div class="lab">Mutation</div>
<pre class="diff"><span class="del">- {e(s['old'].strip())}</span>
<span class="add">+ {e(s['new'].strip())}</span></pre>
{detail}
<div class="lab">Extractor round-trip gate</div><p class="fine">{
 "passes — the mutation reached Lean faithfully" if r['rt']=='0' else ("not run" if not r['rt'] else "FAILS")
}{f" · lake build {r['time']}s" if r['time'] else ""}</p>
</details></td></tr>'''

rows="".join(row(r) for r in rounds)

DISPO_SECTIONS=[
 ("A","fix","Should be caught — the check already exists, unwired","rounds 7, 16, 22",
  "<code>AirsClean/Binary/Circuit.lean</code> defines all eight byte-table messages "
  "<code>lookupMessage0 … lookupMessage7</code>, and that module <b>is</b> in "
  "<code>root_soundness</code>’s import closure — <code>Soundness.lean</code> consumes them. So the "
  "model makes eight concrete claims about ZisK’s <code>BINARY_TABLE</code> tuples, and "
  "<code>Binary/Wiring.lean</code> ties exactly one of them, <code>lookupMessage7</code>, to "
  "<code>link_Binary_10</code>."
  "<br><br>The extractor <b>already emits</b> <code>link_Binary_7</code>, <code>_8</code>, "
  "<code>_9</code> and <code>_11</code> — the very constraints these rounds mutated — validated "
  "against its standard lookup template and consumed by nothing. The correspondence was not "
  "designed: rounds 4 and 25 landed on constraint 10 and were caught; 7, 16 and 22 landed on 8, 9 "
  "and 11 and were not. The fix is one more module shaped like the one that already exists."),
 ("B","fix","Should be caught — but the extractor must learn the template first","rounds 32, 38, 46",
  "<code>BinaryAdd</code> c5 and <code>Arith</code> c61 are <code>proves_operation</code> emissions "
  "on the 5000 bus. They are among the 79 constraints the extractor emits as "
  "<code>constraintOnly_*</code> with no validated template, and it says so in its own manifest: "
  "<code>airStatus_BinaryAdd.unlinkedMixedConstraintCount = 3</code>, likewise for Arith. Meanwhile "
  "the model supplies the tuple itself — <code>BinaryAdd/Bridge.lean:62</code> hard-codes "
  "<code>op := 10</code> — and both bridges sit inside <code>root_soundness</code>’s closure."
  "<br><br>Half of this is written down: <code>air-inventory.md</code> marks <code>Buses.lean</code> "
  "and <code>MemoryBuses.lean</code> <b>“No consumer”</b>. What is not written down is the "
  "consequence — the model’s substitute tuple is an unchecked claim about ZisK."),
 ("C","bug","Should be caught — and this one is a plain bug","rounds 5, 26, 33, 36",
  "Three defects stack. <b>(1)</b> <code>pil-extract/src/arith_table.rs:109</code> emits "
  "<code>import ZiskFv.Fundamentals.Goldilocks</code>; that module has not existed since "
  "<code>84828e96</code> — the sibling <code>MemAlignRom.lean</code> uses the correct "
  "<code>ZiskFv.Field.Goldilocks</code> — so <code>Extraction.ArithTable</code> <b>cannot "
  "elaborate</b>. <b>(2)</b> It is absent from <code>lakefile.toml</code>’s globs, which is why "
  "nobody noticed; <code>check-module-reachability.py</code> exists precisely to fail on modules "
  "<code>lake build</code> never compiles, but walks <code>ZiskFv/</code> only and never looks at "
  "<code>build/extraction/</code>. <b>(3)</b> The data reaches the proof by hand transcription — 74 "
  "literal rows in <code>AirsClean/ArithTable.lean:109</code>, in the closure, and the source "
  "<code>ArithTableProjections</code> uses to derive <code>na = MSB(op1)</code> for the signed-MUL "
  "defect entry."
  "<br><br>Fix the import, add the module to the globs, prove <code>rows = arith_table</code> by "
  "<code>decide</code>, and extend the reachability gate to the generated library."),
 ("D","scope","Known out of scope, documented twice over","round 27",
  "<code>trust/trusted-base.md:896</code> states plainly: <i>“This slice does <b>not</b> claim "
  "register/memory access-ordering soundness.”</i> The same section analyses "
  "<code>main.pil:447</code>’s <code>MAX_RANGE</code> margin down to the zero-margin case and "
  "concludes <i>“<code>447</code> remains genuinely unmodelled and is still an extraction-fidelity "
  "gap.”</i>"
  "<br><br>There is also a mechanical reason the mutation cannot move the proof: the Lean "
  "register-ordering argument comes from <code>Air.Flat.BalancedInteractions</code> being "
  "<b>message-exact</b> plus timestamp separation mod 4, not from ZisK’s range checks. No "
  "<code>MAX_RANGE</code> and no <code>*_reg_prev_mem_step</code> ordering constraint appears "
  "anywhere under <code>ZiskFv/</code>. Worth recording, though, that proof and circuit establish "
  "ordering by <em>different</em> mechanisms, so the Lean side offers no coverage of the circuit’s."),
]
dispo_cards="".join(
 f'<article class="dispo {c}"><header><span class="key">{k}</span><h3>{t}</h3>'
 f'<span class="rn">{rn}</span></header><p>{b}</p></article>'
 for k,c,t,rn,b in DISPO_SECTIONS)

LINKTAB=[("Main",114,70,44),("Mem",25,9,16),("Arith",16,13,3),("BinaryExtension",8,5,3),
 ("MemAlignWriteByte",8,3,5),("MemAlign",7,6,1),("MemAlignByte",7,6,1),("Binary",7,5,2),
 ("MemAlignReadByte",6,5,1),("BinaryAdd",5,2,3)]
linkrows="".join(f'<tr><td><code>{a}</code></td><td class="num">{m}</td><td class="num">{l}</td>'
                 f'<td class="num">{u}</td></tr>' for a,m,l,u in LINKTAB)

MECH=[
 ("The Arith ROM table is never compiled",
  "5, 26, 33, 36",
  "<code>Extraction.ArithTable</code> is absent from <code>lakefile.toml</code>’s "
  "<code>globs</code> and imported by nothing. It could not elaborate if it were: "
  "<code>pil-extract</code> emits <code>import ZiskFv.Fundamentals.Goldilocks</code>, a module "
  "that has not existed since <code>84828e96</code>. The model’s own 74 rows sit in "
  "<code>AirsClean/ArithTable.lean:109</code> as literal <code>#v[…]</code> whose docstring claims "
  "they are “Verbatim from” the generated file — a claim no compiled declaration checks."),
 ("Binary’s byte-table lookup tuples are unwelded",
  "7, 16, 22",
  "<code>BinaryMirrorWeld</code> welds <code>Binary</code> constraints 0–6; "
  "<code>Binary/Wiring.lean</code> welds constraint 10. Constraints 7–9 and 11–13 — the remaining "
  "<code>BINARY_TABLE</code> lookups — are named nowhere under <code>ZiskFv/</code>. Rounds 4 and 25 "
  "landed on constraint 10 and were caught; rounds 7, 16 and 22 landed one constraint away and were not."),
 ("An AIR’s row equations are welded; the tuple it publishes is not",
  "32, 38, 46",
  "<code>BinaryAdd</code> constraint 5 (the bus opcode) and <code>Arith</code> constraint 61 (the bus "
  "result) are outside every welded set. BinaryAdd can advertise <code>OP_SUB</code> while computing "
  "<code>a + b</code>; Arith can transpose the two 16-bit limbs of its announced result. The model "
  "supplies these tuples itself — <code>BinaryAdd/Bridge.lean:62</code> hard-codes <code>op := 10</code>. "
  "Two independent random draws (38 and 46) hit the same constraint."),
 ("Range-check ids are unwelded",
  "27",
  "Widening <code>MAX_RANGE</code> by one on the register-ordering check changes nine constraints "
  "across four AIRs — <code>Main</code> 41 &amp; 142, <code>MemAlign</code> 33–36 &amp; 38, "
  "<code>MemAlignByte</code> 12, <code>MemAlignWriteByte</code> 10 — and not one is named by a theorem. "
  "That check is what forces a register read to name the most recent previous access."),
]
mech="".join(
 f'<article class="mech"><header><h3>{t}</h3><span class="rn">rounds {rn}</span></header><p>{b}</p></article>'
 for t,rn,b in MECH)

HTML=f'''<title>ZisK Mutation Sweep</title>
<link rel="stylesheet" href="https://fonts.googleapis.com/css2?family=IBM+Plex+Mono:wght@400;500&family=IBM+Plex+Sans+Condensed:wght@600;700&family=IBM+Plex+Sans:wght@400;500;600&display=swap">
<style>
:root{{
  --paper:#F4F5F7; --surface:#FFFFFF; --ink:#12151A; --muted:#5A6272; --faint:#828B9B;
  --rule:#DCE0E6; --rule-soft:#E9ECF0;
  --accent:#2F5D62; --caught:#2E6F4E; --missed:#9A5B12; --ctrl:#5A6272; --nontest:#98A0AE;
  --caught-bg:#E4F0E9; --missed-bg:#F7ECD9; --ctrl-bg:#E8EAEE; --nontest-bg:#EFF1F4;
  --code-bg:#EDEFF3;
}}
@media (prefers-color-scheme:dark){{ :root:not([data-theme="light"]){{
  --paper:#101318; --surface:#171B22; --ink:#E4E8EE; --muted:#9BA5B5; --faint:#78828F;
  --rule:#272D37; --rule-soft:#1F242C;
  --accent:#74B3AA; --caught:#63AB80; --missed:#D0973F; --ctrl:#8C96A6; --nontest:#5C6472;
  --caught-bg:#182A20; --missed-bg:#2C2213; --ctrl-bg:#1D222A; --nontest-bg:#171B22;
  --code-bg:#1C212A;
}} }}
:root[data-theme="dark"]{{
  --paper:#101318; --surface:#171B22; --ink:#E4E8EE; --muted:#9BA5B5; --faint:#78828F;
  --rule:#272D37; --rule-soft:#1F242C;
  --accent:#74B3AA; --caught:#63AB80; --missed:#D0973F; --ctrl:#8C96A6; --nontest:#5C6472;
  --caught-bg:#182A20; --missed-bg:#2C2213; --ctrl-bg:#1D222A; --nontest-bg:#171B22;
  --code-bg:#1C212A;
}}
*{{box-sizing:border-box}}
body{{background:var(--paper);color:var(--ink);
  font:400 16px/1.62 "IBM Plex Sans","Segoe UI",system-ui,sans-serif;
  -webkit-font-smoothing:antialiased;padding:0 0 6rem}}
.wrap{{max-width:78rem;margin:0 auto;padding:0 1.75rem;display:flex;flex-direction:column;gap:3.25rem}}
.col{{max-width:66ch}}
h1,h2,h3{{font-family:"IBM Plex Sans Condensed","IBM Plex Sans",sans-serif;text-wrap:balance;margin:0}}
h1{{font-weight:700;font-size:clamp(2.1rem,4.6vw,3.1rem);line-height:1.05;letter-spacing:-.015em}}
h2{{font-weight:700;font-size:1.55rem;letter-spacing:-.005em}}
h3{{font-weight:600;font-size:1.06rem}}
p{{margin:0 0 .85rem}}
code{{font-family:"IBM Plex Mono",ui-monospace,monospace;font-size:.86em;
  background:var(--code-bg);padding:.09em .34em;border-radius:3px}}
pre{{font-family:"IBM Plex Mono",ui-monospace,monospace;font-size:.78rem;line-height:1.55;
  background:var(--code-bg);padding:.8rem .95rem;border-radius:4px;overflow-x:auto;margin:.35rem 0 1rem}}
pre code{{background:none;padding:0}}
a{{color:var(--accent)}}
:focus-visible{{outline:2px solid var(--accent);outline-offset:2px}}

header.top{{border-bottom:1px solid var(--rule);padding:3.5rem 0 2.25rem;margin-bottom:0}}
.eyebrow{{font-family:"IBM Plex Mono",monospace;font-size:.72rem;letter-spacing:.14em;
  text-transform:uppercase;color:var(--accent);margin:0 0 1rem}}
.lede{{font-size:1.16rem;color:var(--muted);max-width:60ch;margin-top:1.15rem}}
.lede b{{color:var(--ink);font-weight:600}}

.scores{{display:flex;flex-wrap:wrap;gap:0;margin-top:2.25rem;border:1px solid var(--rule);
  border-radius:5px;overflow:hidden;background:var(--surface)}}
.score{{flex:1 1 8rem;padding:1rem 1.15rem;border-right:1px solid var(--rule-soft)}}
.score:last-child{{border-right:0}}
.score .n{{font-family:"IBM Plex Sans Condensed",sans-serif;font-weight:700;font-size:2rem;
  line-height:1;font-variant-numeric:tabular-nums}}
.score .l{{font-size:.79rem;color:var(--muted);margin-top:.3rem;display:block}}
.score.c .n{{color:var(--caught)}} .score.m .n{{color:var(--missed)}}

.gridwrap{{display:flex;flex-direction:column;gap:.85rem}}
.grid{{display:grid;grid-template-columns:repeat(auto-fill,minmax(2.15rem,1fr));gap:4px;max-width:44rem}}
.cell{{aspect-ratio:1;border-radius:3px;display:grid;place-items:center;text-decoration:none;
  font-family:"IBM Plex Mono",monospace;font-size:.66rem;font-variant-numeric:tabular-nums;
  border:1px solid transparent;transition:transform .12s ease}}
.cell:hover{{transform:scale(1.14)}}
.cell.caught{{background:var(--caught-bg);color:var(--caught);border-color:var(--caught)}}
.cell.missed{{background:var(--missed-bg);color:var(--missed);border-color:var(--missed)}}
.cell.control{{background:var(--ctrl-bg);color:var(--ctrl);border-color:var(--ctrl)}}
.cell.nontest{{background:var(--nontest-bg);color:var(--nontest);border-color:var(--rule)}}
.legend{{display:flex;flex-wrap:wrap;gap:1.1rem;font-size:.8rem;color:var(--muted)}}
.legend i{{width:.72rem;height:.72rem;border-radius:2px;display:inline-block;margin-right:.4rem;
  vertical-align:-1px;border:1px solid}}
.legend .caught{{background:var(--caught-bg);border-color:var(--caught)}}
.legend .missed{{background:var(--missed-bg);border-color:var(--missed)}}
.legend .control{{background:var(--ctrl-bg);border-color:var(--ctrl)}}
.legend .nontest{{background:var(--nontest-bg);border-color:var(--rule)}}

.pipe{{font-family:"IBM Plex Mono",monospace;font-size:.76rem;line-height:1.8;color:var(--muted);
  background:var(--surface);border:1px solid var(--rule);border-radius:5px;
  padding:1.1rem 1.25rem;overflow-x:auto;white-space:pre}}
.pipe b{{color:var(--accent);font-weight:500}}

.dispos{{display:grid;gap:1rem;grid-template-columns:repeat(auto-fit,minmax(23rem,1fr));margin-top:.5rem}}
.dispo{{background:var(--surface);border:1px solid var(--rule);border-left:3px solid var(--missed);
  border-radius:4px;padding:1.15rem 1.3rem}}
.dispo.scope{{border-left-color:var(--accent)}} .dispo.bug{{border-left-color:var(--missed)}}
.dispo header{{display:grid;grid-template-columns:auto 1fr;gap:.55rem .8rem;align-items:baseline;
  margin-bottom:.7rem}}
.dispo .key{{font-family:"IBM Plex Sans Condensed",sans-serif;font-weight:700;font-size:1.1rem;
  color:var(--missed);grid-row:span 2}}
.dispo.scope .key{{color:var(--accent)}}
.dispo .rn{{font-family:"IBM Plex Mono",monospace;font-size:.72rem;color:var(--faint);grid-column:2}}
.dispo p{{margin:0;font-size:.91rem;color:var(--muted)}}
.dispo code{{color:var(--ink)}}
.dtag{{display:inline-block;margin-top:.3rem;font-family:"IBM Plex Mono",monospace;font-size:.66rem;
  color:var(--faint);max-width:11rem;line-height:1.35}}
.dtag.scope{{color:var(--accent)}}
.oblig{{display:grid;gap:1rem;grid-template-columns:repeat(auto-fit,minmax(19rem,1fr))}}
.ob{{background:var(--surface);border:1px solid var(--rule);border-radius:4px;padding:1.1rem 1.25rem;
  border-top:3px solid var(--rule)}}
.ob.proved{{border-top-color:var(--caught)}} .ob.open{{border-top-color:var(--missed)}}
.ob .k{{display:block;font-family:"IBM Plex Mono",monospace;font-size:.7rem;letter-spacing:.09em;
  text-transform:uppercase;color:var(--faint);margin-bottom:.45rem}}
.ob b{{font-family:"IBM Plex Sans Condensed",sans-serif;font-size:1.25rem;display:block}}
.ob.proved b{{color:var(--caught)}} .ob.open b{{color:var(--missed)}}
.ob p{{margin:.5rem 0 0;font-size:.89rem;color:var(--muted)}}
.verdictbox{{border-left:3px solid var(--accent);padding:.15rem 0 .15rem 1.15rem}}
.verdictbox p:last-child{{margin:0;color:var(--muted);font-size:.94rem}}
.mechs{{display:grid;gap:1rem;grid-template-columns:repeat(auto-fit,minmax(20rem,1fr))}}
.mech{{background:var(--surface);border:1px solid var(--rule);border-left:3px solid var(--missed);
  border-radius:4px;padding:1.1rem 1.25rem}}
.mech header{{display:flex;justify-content:space-between;align-items:baseline;gap:1rem;margin-bottom:.6rem}}
.mech .rn{{font-family:"IBM Plex Mono",monospace;font-size:.72rem;color:var(--missed);white-space:nowrap}}
.mech p{{margin:0;font-size:.91rem;color:var(--muted)}}
.mech code{{color:var(--ink)}}

table{{width:100%;border-collapse:collapse;font-size:.87rem}}
.tablewrap{{overflow-x:auto;border:1px solid var(--rule);border-radius:5px;background:var(--surface)}}
th{{font-family:"IBM Plex Sans Condensed",sans-serif;font-weight:600;text-align:left;
  font-size:.76rem;letter-spacing:.05em;text-transform:uppercase;color:var(--muted);
  padding:.7rem .8rem;border-bottom:1px solid var(--rule);white-space:nowrap;
  position:sticky;top:0;background:var(--surface)}}
td{{padding:.62rem .8rem;border-bottom:1px solid var(--rule-soft);vertical-align:top}}
.num{{font-variant-numeric:tabular-nums;text-align:right;white-space:nowrap}}
tr.v-caught td:first-child{{box-shadow:inset 3px 0 0 var(--caught)}}
tr.v-missed td:first-child{{box-shadow:inset 3px 0 0 var(--missed)}}
tr.v-control td:first-child{{box-shadow:inset 3px 0 0 var(--ctrl)}}
tr.det td{{border-bottom:1px solid var(--rule);padding-top:0}}
tr.det summary{{cursor:pointer;font-size:.79rem;color:var(--faint);
  font-family:"IBM Plex Mono",monospace;padding:.2rem 0}}
tr.det[open] summary{{color:var(--accent)}}
.tag{{font-family:"IBM Plex Mono",monospace;font-size:.76rem;white-space:nowrap}}
.op{{font-size:.74rem;white-space:nowrap}}
.site{{min-width:14rem}} .why{{color:var(--muted);min-width:18rem;font-size:.84rem}}
.fine{{font-size:.8rem;color:var(--faint)}}
.pill{{display:inline-block;font-size:.73rem;font-weight:600;padding:.13rem .5rem;border-radius:99px;
  border:1px solid;white-space:nowrap}}
.pill.caught{{color:var(--caught);border-color:var(--caught);background:var(--caught-bg)}}
.pill.missed{{color:var(--missed);border-color:var(--missed);background:var(--missed-bg)}}
.pill.control{{color:var(--ctrl);border-color:var(--ctrl);background:var(--ctrl-bg)}}
.pill.nontest{{color:var(--nontest);border-color:var(--rule);background:var(--nontest-bg)}}
b.caught{{color:var(--caught)}} b.missed{{color:var(--missed)}}
.lab{{font-family:"IBM Plex Sans Condensed",sans-serif;font-size:.72rem;letter-spacing:.08em;
  text-transform:uppercase;color:var(--faint);margin:.9rem 0 .25rem}}
.diff .del{{color:var(--missed)}} .diff .add{{color:var(--caught)}}
.err{{border-left:2px solid var(--missed)}}
.bar{{display:inline-block;width:5rem;height:.42rem;background:var(--rule);border-radius:2px;
  overflow:hidden;margin-right:.5rem;vertical-align:1px}}
.bar i{{display:block;height:100%;background:var(--accent)}}
b.in{{color:var(--accent)}} .out{{color:var(--faint)}}
footer{{border-top:1px solid var(--rule);padding-top:1.5rem;color:var(--faint);font-size:.82rem}}
@media (prefers-reduced-motion:reduce){{*{{transition:none!important}}}}
</style>

<div class="wrap">
<header class="top">
  <p class="eyebrow">zisk-fv · mutation testing · c031ac03</p>
  <h1>Breaking ZisK on purpose,<br>52 times</h1>
  <p class="lede">Each round injects one defect into the pinned ZisK v0.17.0 sources, recompiles the
  circuit with <code>pil2-compiler</code>, re-runs <code>tools/pil-extract</code>, and rebuilds the Lean
  proof. <b>35 mutations genuinely changed ZisK’s compiled constraint system. The proof caught 24 and
  missed 11.</b></p>
  <div class="scores">
    <div class="score"><span class="n">52</span><span class="l">mutations attempted</span></div>
    <div class="score"><span class="n">35</span><span class="l">valid tests</span></div>
    <div class="score c"><span class="n">24</span><span class="l">caught — build fails</span></div>
    <div class="score m"><span class="n">11</span><span class="l">missed — build green</span></div>
    <div class="score"><span class="n">3</span><span class="l">commutativity controls</span></div>
  </div>
</header>

<section class="gridwrap">
  <h2>Every round</h2>
  <div class="grid">{grid}</div>
  <div class="legend">
    <span><i class="caught"></i>caught — <code>lake build</code> fails</span>
    <span><i class="missed"></i>missed — build still green</span>
    <span><i class="control"></i>control — polynomial unchanged</span>
    <span><i class="nontest"></i>not a test</span>
  </div>
</section>

<section class="col">
  <h2>The pipeline under test</h2>
  <p>Mutations enter at the leftmost box, which is where a real ZisK bug would live.</p>
</section>
<div class="pipe"><b>zisk/**/*.pil</b>  ──pil2-compiler──▶  zisk.pilout  ──tools/pil-extract──▶  build/extraction/Extraction/*.lean
                                                                       │
                                   ZiskFv/** (hand-maintained model) ──┴──▶  <b>lake build</b></div>

<section class="col">
  <h2>Two controls, so a delta means something</h2>
  <p>Recompiling the <em>unmutated</em> pinned tree and re-extracting yields Lean output that is
  <b>byte-identical</b> to the pinned <code>nix run .#populate</code> extraction. Any Lean delta a round
  reports comes from the mutation and nothing else in the harness.</p>
  <p><code>zisk.pilout</code> turns out not to be byte-reproducible — two compiles of identical source
  differ in 4.3 M of 4.4 M bytes, and in length. Both extract to the same Lean, and the polynomial
  normal form of every constraint in the ten extracted AIRs agrees. So pilout bytes are never used as
  evidence here; the polynomial normal form is, computed with the repository’s own
  <code>pilout_wire</code> / <code>pilout_atoms</code> / <code>poly</code> modules. A round whose
  mutation only re-associates an expression is reported as a control, never as a finding.</p>
  <p>Each round also runs the repository’s own extraction gate,
  <code>tools/pilout-roundtrip/check.py</code>. It passing on a mutated round says the extractor carried
  the bug into Lean faithfully — which is why a missed round cannot be blamed on the extractor.</p>
</section>

<section>
  <h2 class="col">Where the misses come from</h2>
  <div class="mechs">{mech}</div>
</section>

<section class="col">
  <h2>What caught the 24</h2>
  <p>Twenty-one of the 24 were caught by a module that only <code>ZiskFv.lean</code> imports. The mirror
  welds do their job — a dropped identity, a flipped booleanity sign, an ungated selector and a
  renumbered constraint list all turn the build red, usually with a legible <code>Iff.rfl</code> type
  mismatch printing the model’s predicate against the generated one. But they are audit modules:
  the import closure of <code>ZiskFv.Soundness</code> is 637 modules and reaches exactly two generated
  ones, <code>Extraction.LookupWiring</code> and <code>Extraction.MemAlignRom</code>. What the welds
  defend is the repository’s build, not the theorem’s statement.</p>
</section>
<div class="tablewrap"><table>
<thead><tr><th>module</th><th class="num">caught</th><th>relation to <code>root_soundness</code></th></tr></thead>
<tbody>{catch_rows}</tbody></table></div>

<section class="col">
  <h2>How much of the extraction any theorem names</h2>
  <p><code>constraint_&lt;i&gt;_every_row</code> is the generated form of pilout constraint <i>i</i>.
  The unnamed 48 % are mostly the challenge-mixing (<code>gsum</code>/logUp) constraints that carry the
  bus and lookup tuples, plus all of <code>BinaryExtension</code>. They are elaborated by
  <code>lake build</code>, but no theorem relates them to anything.</p>
</section>
<div class="tablewrap"><table>
<thead><tr><th>AIR</th><th class="num">emitted</th><th class="num">named</th><th class="num">coverage</th></tr></thead>
<tbody>{cov_rows}
<tr><td><b>total</b></td><td class="num"><b>{tot_e}</b></td><td class="num"><b>{tot_n}</b></td>
<td class="num"><b>{100*tot_n//tot_e}%</b></td></tr></tbody></table></div>

<section class="col">
  <h2>The welds are definitional, not semantic</h2>
  <p>Rounds 6, 21 and 51 rewrite one term of an Arith identity into a commutative image of itself.
  The polynomial normal form says nothing changed. All three fail the build anyway. That is the welds
  working as designed — they are <code>Iff.rfl</code> equalities against the generated term, so they pin
  the <em>syntactic form</em> of each constraint, strictly stronger than pinning the polynomial. The
  cost is that a benign reordering in ZisK’s PIL turns the repository red and needs the mirrors updated
  by hand.</p>
</section>

<section class="col">
  <h2>Should each miss have been caught?</h2>
  <p>“Missed” and “should have been caught” are different claims. A miss matters only if the mutated
  element is something the <b>model asserts about ZisK</b> and that <code>root_soundness</code> then
  leans on. The test is mechanical: is the mutated constraint represented in a module inside the
  import closure of <code>ZiskFv.Soundness</code>, and is that representation tied to the extraction
  by anything?</p>
  <p>One number organises the answer. <code>pil-extract</code> emits <b>124
  <code>ValidatedLink</code>s</b> — lookup and bus templates it has already proved match the generated
  constraint — plus <b>79 <code>constraintOnly</code></b> entries for mixed constraints it could not
  template. <code>ZiskFv/</code> consumes <b>6</b> of the 124 and <b>none</b> of the 79.</p>
</section>
<div class="tablewrap"><table>
<thead><tr><th>AIR</th><th class="num">mixed constraints</th><th class="num">extractor linked</th>
<th class="num">could not link</th></tr></thead>
<tbody>{linkrows}
<tr><td><b>total</b></td><td class="num"><b>203</b></td><td class="num"><b>124</b></td>
<td class="num"><b>79</b></td></tr></tbody></table></div>
<section><div class="dispos">{dispo_cards}</div></section>
<section class="col">
  <div class="verdictbox">
    <p><b>Ten of the eleven misses are fidelity gaps that should close. One is a documented scope
    exclusion.</b></p>
    <p>None of the ten is a false theorem — <code>root_soundness</code> is true of the model it is
    stated over. What is unchecked is whether that model is still ZisK, and for the bus and lookup
    tuples the extractor has already done most of the work needed to check it.</p>
  </div>
</section>

<section class="col">
  <h2>What a passing build does and does not mean</h2>
  <p>A missed round does not mean the mutated circuit was re-verified and found sound. Nothing read
  it. A green <code>lake build</code> attests two things, and only one of them is a Lean theorem.</p>
</section>
<div class="oblig">
  <div class="ob proved"><span class="k">obligation 1</span><b>model &rArr; Sail</b>
    <p><code>ZiskFv.Compliance.root_soundness</code>. Proved. No mutation touches it.</p></div>
  <div class="ob open"><span class="k">obligation 2</span><b>ZisK &rArr; model</b>
    <p>Not a theorem — the mirror welds, the wiring modules, the trust ledger, human review.
    <b>All eleven misses are here.</b></p></div>
</div>
<section class="col">
  <p>Mutating ZisK changes <code>build/extraction/Extraction/*.lean</code>. It does not change
  <code>ZiskFv/**</code>. <code>root_soundness</code> is stated over the hand-written model, so after
  a mutation it proves exactly what it proved before, from inputs that never included the mutated
  constraint.</p>
  <p><b>Which way the failure runs.</b> The theorem does not become false — it silently stops
  applying. It takes an <code>AcceptedZiskTrace</code>, and the model keeps demanding the original
  constraint after ZisK has stopped enforcing it, so traces the mutated machine accepts are no longer
  <code>AcceptedZiskTrace</code>s. The hypothesis is unfulfillable for exactly the behaviour the
  mutation introduced, and the theorem says nothing about it while continuing to look like it does.
  Loss of applicability, not a false conclusion, and no signal either way.</p>
  <p><b>The narrow sense in which the mutant is “still a validly constrained circuit”.</b> The model
  remains a coherent constraint system that implies Sail. But no new circuit was verified: the
  <em>old</em> circuit kept being verified while the deployed one drifted away from it. That
  distinction is the entire content of obligation 2.</p>
  <p><b>Worked example — round 32.</b> Mutated ZisK’s <code>BinaryAdd</code> rows announce
  <code>OP_SUB</code> on the 5000 bus while computing <code>a + b</code>, so a prover could discharge
  a <code>SUB</code> request with an addition — and the <code>Binary</code> AIR is a second, correct
  <code>SUB</code> provider, making this an extra wrong provider for a live opcode rather than merely
  an unsatisfiable circuit. On the Lean side <code>BinaryAdd/Bridge.lean:62</code> still reads
  <code>op := 10</code>, the balance argument still matches Main’s <code>SUB</code> against the
  <code>Binary</code> AIR, and <code>root_soundness</code> goes through — describing a machine that no
  longer exists.</p>
  <p><b>What was demonstrated, and what was not.</b> Each missed round demonstrates that the model
  stopped describing ZisK: the polynomial normal form changed, the round-trip gate confirms the
  extractor carried that change into Lean faithfully, the build log shows Lean re-elaborated the
  affected modules, and the build stayed green. <b>No forged proof was built against a mutated
  ZisK.</b> That needs the prover, the way
  <code>ZISK-DEFECT-ARITH-MUL-SIGNED-WITNESS-SOUNDNESS</code> was demonstrated end to end under
  Docker. The unsoundness of each mutant here is an argument from its constraint change, not an
  executed forgery.</p>
  <p><b>The controls invert the point.</b> Rounds 6, 21 and 51 rewrite one term into a commutative
  image of itself. The polynomial is identical and all three turn the build <b>red</b>, because the
  welds are <code>Iff.rfl</code> equalities against the generated term. So the build’s sensitivity
  currently tracks <em>syntactic identity of a 52 % subset</em> of the extracted constraints, not
  soundness. Both directions are worth closing: the false negatives cost fidelity, the false
  positives cost maintenance every time ZisK reorders a product.</p>
</section>

<section>
  <h2 class="col">Round by round</h2>
  <p class="col fine">Open a row for the source diff, the Lean error, and the argument that the mutated
  constraint is genuinely part of ZisK’s RV64IM soundness surface.</p>
</section>
<div class="tablewrap"><table>
<thead><tr><th class="num">#</th><th>AIR</th><th>operator</th><th>site</th>
<th>did ZisK change?</th><th>build</th><th>verdict</th></tr></thead>
<tbody>{rows}</tbody></table></div>

<footer class="col">
  <p>Sites enumerated mechanically from twelve in-scope ZisK source files and sampled uniformly
  (seeds 20260904 / 20260905 / 20260906). Pinned inputs: <code>zisk-src</code> @ <code>b632745</code>
  (v0.17.0), <code>pil2-compiler</code> v0.9.0, <code>pil2-proofman</code> v0.17.0 — the same store paths
  <code>nix/zisk-pilout.nix</code> uses. Baseline <code>lake build</code> at <code>c031ac03</code>:
  green, 9172 jobs. Build <em>times</em> are not comparable across rounds — rounds are chained and
  rebuild incrementally; only the exit code is evidence. The worktree was restored to the pinned
  pilout and extraction afterwards, round-trip gate 355/355, build green.</p>
</footer>
</div>'''
open(f"{SP}/zisk-mutation-sweep.html","w").write(HTML)
print("wrote", f"{SP}/zisk-mutation-sweep.html", len(HTML), "bytes")
print("valid",len(nv),"caught",len(caught),"missed",len(missed),"ctrl",len(ctrl),"nontest",len(nont))
