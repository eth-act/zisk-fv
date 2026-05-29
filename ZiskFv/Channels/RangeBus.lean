import Clean.Circuit.Channel
import Clean.Circuit.Provable
import Clean.Utils.Tactics.ProvableStructDeriving
import ZiskFv.Field.Goldilocks

/-!
# RangeBus typed channel (byte-range lookup table)

ZisK's byte-range bus: AIRs whose witness columns are bit-width-bounded
(`bits(8)` annotation in PIL) pull from the byte-range channel,
asserting `0 ≤ value < 256`. The provider is the static table
`{0, 1, ..., 255}`.

This is a `StaticLookupChannel` — a special form where the channel's
table is fixed and its `Guarantees` is set-membership in that table.

## Trust note

Same pattern as the other channels -- no new axioms. T7 retired the former
generic range-bus trust boundary; remaining byte-range facts are routed
through concrete Clean/static lookup witnesses for the selected provider row.
-/

namespace ZiskFv.Channels.RangeBus

open Goldilocks

/-- Single-slot field message — the byte-range channel carries one
    field element per interaction. Reuses Clean's existing
    `field` TypeMap pattern. -/
abbrev ByteMsg (F : Type) := field F

/-- Lift a single FGL value into a `ByteMsg` (i.e. into the
    `field FGL` TypeMap). -/
@[reducible]
def ByteMsg.ofFGL (x : FGL) : ByteMsg FGL := x

/-- The byte-range static lookup table: `{0, 1, ..., 255}` viewed as
    `FGL` values. -/
def BytesTable : StaticLookupChannel FGL field where
  name := "ByteRange"
  -- The list of 256 byte values, lifted into FGL via Nat → FGL coercion.
  table := (List.finRange 256).map (fun i => (i.val : FGL))
  Guarantees msg := msg.val < 256
  guarantees_iff := by
    intro (msg : FGL)
    simp only [List.mem_map, List.mem_finRange, true_and]
    constructor
    · intro h_lt
      refine ⟨⟨msg.val, h_lt⟩, ?_⟩
      have : (msg.val : FGL) = msg := by
        apply Fin.ext
        simp
      simp [this]
    · rintro ⟨⟨b, hb⟩, h_eq⟩
      rw [← h_eq]
      simp [Fin.val_natCast, Nat.mod_eq_of_lt
        (Nat.lt_of_lt_of_le hb (by decide : (256 : ℕ) ≤ GL_prime))]
      exact hb

/-- The byte-range channel — the typed `Channel` view of the static
    lookup table. Pulling from this channel gives `msg.val < 256`. -/
abbrev BytesChannel : Channel FGL field :=
  Channel.fromStatic FGL field BytesTable

end ZiskFv.Channels.RangeBus
