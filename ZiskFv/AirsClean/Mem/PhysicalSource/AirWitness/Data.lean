import ZiskFv.AirsClean.Mem.PhysicalSource.Columns
import ZiskFv.AirsClean.Mem.Stage2.PolynomialRow
import ZiskFv.AirsClean.Mem.Stage2.Native
import ZiskFv.AirsClean.Mem.Row

/-! Supplemental chosen Mem AIR image, not a native execution or an accepted
world. Algebraic values below are explicit constants and a scalar arithmetic
progression; no gsum is repacked from a generated constraint or caller promise.
All extension coefficients are retained. The chosen alpha=0/gamma=1 blocks are
actual three-coefficient data, not a restriction on production challenges.
PIL b632 mem.pil103–175,195–241,263–286,365–397,403–440; proofman ff0e33a9
std_sum.pil304–307,571–599,640–696. Physical rotations come only from the
existing source-owned View/NativeSetup API. -/
namespace ZiskFv.AirsClean.Mem.PhysicalSource.AirWitness

open Goldilocks
open ZiskFv.AirsClean.MemAlignWriteByte.RawSource.Native
open Extraction.LookupWiring

abbrev Index := PhysicalIndex
abbrev N := Stage1.SourceColumns.physicalRows

def address : FGL := 335544321
def previousAddress : FGL := 335544320

def firstFlag (row : Index) : FGL := if row.val = 0 then 1 else 0

def primary (row : Index) : Vector FGL 13 :=
  #v[address, 0, 0, firstFlag row, 0, 0, 0, 0, 0, 0, 0, 0, 1 - firstFlag row]

def baseAir : Vector FGL 15 :=
  #v[0, 1, 1, 0, 0, 0, previousAddress, 0, 0, 0, address, 0, 0, 65534, 1023]

def cluster : FGL := -((104 : FGL)⁻¹)
def delta : FGL := -((104 : FGL)⁻¹) - (105 : FGL)⁻¹

def running (row : Index) : Stage2.Ext3 FGL :=
  Stage2.Ext3.ofBase (((row.val + 1 : Nat) : FGL) * delta)

def extensionWitness (row : Index) (column : Fin 3) : Stage2.Ext3 FGL :=
  match column.val with
  | 0 => running row
  | 1 => Stage2.Ext3.ofBase cluster
  | _ => 0

def alpha : Stage2.Ext3 FGL := Stage2.Ext3.ofBase 0
def gamma : Stage2.Ext3 FGL := Stage2.Ext3.ofBase 1

def direct (index : Fin 6) : Stage2.Ext3 FGL :=
  if index.val = 0 then Stage2.Ext3.ofBase (-((12 : FGL)⁻¹))
  else if index.val = 1 then 0 else Stage2.Ext3.ofBase cluster

/-- Closed numeric sum of the explicit per-row range contributions and direct
terms. This is not defined by reading the finalizer expression or its gsum cell. -/
def groupResult : Stage2.Ext3 FGL :=
  Stage2.Ext3.ofBase (-(((N : Nat) : FGL) + 4) * (104 : FGL)⁻¹ -
    ((N : Nat) : FGL) * (105 : FGL)⁻¹ - (12 : FGL)⁻¹)

def primaryRow (row : Index) : MemRow FGL where
  addr := (primary row)[0]
  step := (primary row)[1]
  sel := (primary row)[2]
  addr_changes := (primary row)[3]
  step_dual := (primary row)[4]
  sel_dual := (primary row)[5]
  value_0 := (primary row)[6]
  value_1 := (primary row)[7]
  wr := (primary row)[8]
  previous_step := (primary row)[9]
  increment_0 := (primary row)[10]
  increment_1 := (primary row)[11]
  read_same_addr := (primary row)[12]

variable {source : SourceObject FGL} {resolved : ResolvedOccurrence source}

/-- Independent source c0–c23, with actual signed/cyclic row semantics. -/
def segmentResidual (view : View resolved) (row : Index) (equation : Fin 24) : FGL :=
  let w := primary row
  let p := primary (view.previous row)
  let a := baseAir
  let l := firstFlag row
  let ln := firstFlag (view.next row)
  let carriedStep := p[5] * (p[4] - p[1]) + p[1]
  let previousAddr := l * (a[6] - p[0]) + p[0]
  let previousLo := l * (a[3] - p[6]) + p[6]
  let previousHi := l * (a[4] - p[7]) + p[7]
  let ds := w[1] - w[9] + (1 - w[8])
  match equation.val with
  | 0 => a[1] * (1 - a[1])
  | 1 => a[2] * (1 - a[2])
  | 2 => a[1] * a[0]
  | 3 => w[5] * (1 - w[5])
  | 4 => (1 - w[2]) * w[5]
  | 5 => w[2] * (1 - w[2])
  | 6 => w[3] * (1 - w[3])
  | 7 => w[8] * (1 - w[8])
  | 8 => w[8] * (1 - w[2])
  | 9 => ln * (w[6] - a[7])
  | 10 => ln * (w[7] - a[8])
  | 11 => ln * (w[0] - a[10])
  | 12 => ln * (w[5] * (w[4] - w[1]) + w[1] - a[9])
  | 13 => (a[6] - 335544320) - (a[11] + 65536 * a[12])
  | 14 => (402653183 - a[10]) - (a[13] + 65536 * a[14])
  | 15 => w[9] - (l * (a[5] - carriedStep) + carriedStep)
  | 16 => (w[10] + 4194304 * w[11] + 1) -
      (w[3] * (w[0] - previousAddr - ds) + ds)
  | 17 => (a[1] * l) * (1 - w[3])
  | 18 => w[12] - (1 - w[3]) * (1 - w[8])
  | 19 => (1 - w[3]) * (w[0] - previousAddr)
  | 20 => w[12] * (w[6] - previousLo)
  | 21 => (w[3] * (1 - w[8])) * w[6]
  | 22 => w[12] * (w[7] - previousHi)
  | _ => (w[3] * (1 - w[8])) * w[7]

def polynomialRow (view : View resolved) (row : Index) : Stage2.PolynomialRow where
  addr := address
  step := 0
  sel := 0
  stepDual := 0
  selDual := 0
  valueLo := 0
  valueHi := 0
  wr := 0
  lowIncrement := 0
  highIncrement := 0
  segmentId := 0
  isLastSegment := 1
  previousValueLo := 0
  previousValueHi := 0
  previousStep := 0
  previousAddr := previousAddress
  lastValueLo := 0
  lastValueHi := 0
  lastStep := 0
  lastAddr := address
  distanceBaseLo := 0
  distanceBaseHi := 0
  distanceEndLo := 65534
  distanceEndHi := 1023
  alpha := alpha
  gamma := gamma
  running := running row
  previousRunning := running (view.previous row)
  cluster0 := Stage2.Ext3.ofBase cluster
  cluster1 := 0
  direct0 := direct 0
  direct1 := direct 1
  direct2 := direct 2
  direct3 := direct 3
  direct4 := direct 4
  direct5 := direct 5
  l1 := firstFlag row
  nextL1 := firstFlag (view.next row)
  groupResult := groupResult

/-- Exactly declared source witness widths and the actual local range-check
calls. This is a property of this chosen image, NOT a stronger validator for
unpacked native storage or a Root/acceptance premise. -/
def LocalLookups (row : Index) : Prop :=
  (∀ column : Fin 13, ((primary row)[column]).val < 2 ^ Stage1.SourceColumns.packedWidth column) ∧
  (∀ index : Fin 4, (baseAir[11 + index.val]'(by omega)).val < 2 ^ 16) ∧
  ((primary row)[10]).val < 2 ^ 22 ∧ ((primary row)[11]).val < 2 ^ 16 ∧
  ((primary row)[5] = 1 →
    (((primary row)[4] - (primary row)[1] - (primary row)[8] : FGL)).val < 2 ^ 24)

/-- Closed chosen witness leaf data, not an arbitrary callback/environment. -/
def witnessCell (view : View resolved) (row : Index) (stage column : Nat)
    (rotation : Int) : Option (Stage2.Ext3 FGL) :=
  if stage = 1 then
    if within : column < 13 then
      some (Stage2.Ext3.ofBase ((primary (view.rotate row rotation))[column]))
    else none
  else if stage = 2 then
    if within : column < 3 then some (extensionWitness (view.rotate row rotation) ⟨column, within⟩)
    else none
  else none

def airCell (index : Nat) : Option (Stage2.Ext3 FGL) :=
  if within : index < 15 then some (Stage2.Ext3.ofBase baseAir[index])
  else if within : index < 21 then some (direct ⟨index - 15, by omega⟩)
  else none

def challengeCell (stage index : Nat) : Option (Stage2.Ext3 FGL) :=
  if stage = 2 ∧ index < 2 then some (if index = 0 then alpha else gamma) else none

def fixedCell (view : View resolved) (row : Index) (column : Nat) (rotation : Int) :
    Option (Stage2.Ext3 FGL) :=
  if column < 2 then some (Stage2.Ext3.ofBase (firstFlag (view.rotate row rotation))) else none

def groupCell (index : Nat) : Option (Stage2.Ext3 FGL) :=
  if index = 0 then some groupResult else none

/-- Independent algebraic interpretation of these explicit data. Its native
source recovery is a separate theorem, never an assumed field-function match. -/
def polynomial (view : View resolved) (row : Index) : Expr → Option (Stage2.Ext3 FGL)
  | .constant text => Stage2.literal? text
  | .witness stage column rotation => witnessCell view row stage column rotation
  | .fixed column rotation => fixedCell view row column rotation
  | .airValue index => airCell index
  | .airGroupValue index => groupCell index
  | .challenge stage index => challengeCell stage index
  | .add lhs rhs => return (← polynomial view row lhs) + (← polynomial view row rhs)
  | .sub lhs rhs => return (← polynomial view row lhs) - (← polynomial view row rhs)
  | .mul lhs rhs => return (← polynomial view row lhs) * (← polynomial view row rhs)
  | .neg value => return -(← polynomial view row value)
  | .opaque _ _ => none

end ZiskFv.AirsClean.Mem.PhysicalSource.AirWitness
