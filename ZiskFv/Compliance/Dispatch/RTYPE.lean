import ZiskFv.Compliance.OpEnvelope
import ZiskFv.Equivalence.And
import ZiskFv.Equivalence.Or
import ZiskFv.Equivalence.Slt
import ZiskFv.Equivalence.Sltu
import ZiskFv.Equivalence.Sub
import ZiskFv.Equivalence.Xor

/-!
# Compliance dispatcher (RTYPE+Binary arms)

Extends the dispatcher pattern to the RTYPE+Binary family: SUB, AND,
OR, XOR, SLT, SLTU. Same shape (Valid_Binary + BusRows with 3 mem
entries), same one-line proof body via the canonical equiv_<OP> theorems.

## Trust note

No new axioms.
-/

namespace ZiskFv.Compliance

open Goldilocks
open ZiskFv.Channels
open ZiskFv.Airs.Main (Valid_Main)

variable {state : PreSail.SequentialState RegisterType Sail.trivialChoiceSource}
variable {m : Valid_Main FGL FGL} {r_main : ℕ}

/-- The per-arm v2 conclusion Prop for RTYPE+Binary arms.
    Falls through to `True` for non-RTYPE-Binary arms. -/
def OpEnvelope.exec_eq_rtype_binary
    : OpEnvelope state m r_main → Prop
  | .sub _ r1 r2 rd _ bus _ _ _ _ _ _ _ _ _ =>
      (do
        Sail.writeReg Register.nextPC
          (Sail.BitVec.addInt (← Sail.readReg Register.PC) 4)
        LeanRV64D.Functions.execute
          (instruction.RTYPE (r2, r1, rd, rop.SUB))) state
        = state_effect_via_channels
            ⟨bus.exec_row, [bus.e0, bus.e1, bus.e2]⟩ state
  | .and _ r1 r2 rd _ bus _ _ _ _ _ _ _ _ _ =>
      (do
        Sail.writeReg Register.nextPC
          (Sail.BitVec.addInt (← Sail.readReg Register.PC) 4)
        LeanRV64D.Functions.execute
          (instruction.RTYPE (r2, r1, rd, rop.AND))) state
        = state_effect_via_channels
            ⟨bus.exec_row, [bus.e0, bus.e1, bus.e2]⟩ state
  | .or _ r1 r2 rd _ bus _ _ _ _ _ _ _ _ _ =>
      (do
        Sail.writeReg Register.nextPC
          (Sail.BitVec.addInt (← Sail.readReg Register.PC) 4)
        LeanRV64D.Functions.execute
          (instruction.RTYPE (r2, r1, rd, rop.OR))) state
        = state_effect_via_channels
            ⟨bus.exec_row, [bus.e0, bus.e1, bus.e2]⟩ state
  | .xor _ r1 r2 rd _ bus _ _ _ _ _ _ _ _ _ =>
      (do
        Sail.writeReg Register.nextPC
          (Sail.BitVec.addInt (← Sail.readReg Register.PC) 4)
        LeanRV64D.Functions.execute
          (instruction.RTYPE (r2, r1, rd, rop.XOR))) state
        = state_effect_via_channels
            ⟨bus.exec_row, [bus.e0, bus.e1, bus.e2]⟩ state
  | .slt _ r1 r2 rd _ bus _ _ _ _ _ _ _ _ _ =>
      (do
        Sail.writeReg Register.nextPC
          (Sail.BitVec.addInt (← Sail.readReg Register.PC) 4)
        LeanRV64D.Functions.execute
          (instruction.RTYPE (r2, r1, rd, rop.SLT))) state
        = state_effect_via_channels
            ⟨bus.exec_row, [bus.e0, bus.e1, bus.e2]⟩ state
  | .sltu _ r1 r2 rd _ bus _ _ _ _ _ _ _ _ _ =>
      (do
        Sail.writeReg Register.nextPC
          (Sail.BitVec.addInt (← Sail.readReg Register.PC) 4)
        LeanRV64D.Functions.execute
          (instruction.RTYPE (r2, r1, rd, rop.SLTU))) state
        = state_effect_via_channels
            ⟨bus.exec_row, [bus.e0, bus.e1, bus.e2]⟩ state
  | _ => True

/-- Shared C7 static BinaryTable lookup obligation for RTYPE Binary arms. -/
def OpEnvelope.rtype_binary_logic_static_lookup_soundness
    : OpEnvelope state m r_main → Prop
  | .sub _ _ _ _ v _ _ _ _ _ _ _ _ _ _ =>
      ZiskFv.AirsClean.Binary.StaticLookupSoundness v
  | .and _ _ _ _ v _ _ _ _ _ _ _ _ _ _ =>
      ZiskFv.AirsClean.Binary.StaticLookupSoundness v
  | .or _ _ _ _ v _ _ _ _ _ _ _ _ _ _ =>
      ZiskFv.AirsClean.Binary.StaticLookupSoundness v
  | .xor _ _ _ _ v _ _ _ _ _ _ _ _ _ _ =>
      ZiskFv.AirsClean.Binary.StaticLookupSoundness v
  | .slt _ _ _ _ v _ _ _ _ _ _ _ _ _ _ =>
      ZiskFv.AirsClean.Binary.StaticLookupSoundness v
  | .sltu _ _ _ _ v _ _ _ _ _ _ _ _ _ _ =>
      ZiskFv.AirsClean.Binary.StaticLookupSoundness v
  | _ => True

/-- C7 table-row route for RTYPE bitwise Binary arms.

Unlike `rtype_binary_logic_static_lookup_soundness`, this does not quantify
over a legacy `Valid_Binary` row plus offset. The provider evidence is the
actual lookup-aware Clean Binary table row whose `table.Spec` supplies both
the Binary core constraints and static BinaryTable facts. -/
def OpEnvelope.rtype_bitwise_static_table_row_route
    : OpEnvelope state m r_main → Prop
  | .sub _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ => True
  | .and _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ => True
  | .or _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ => True
  | .xor _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ => True
  | .slt _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ => True
  | .sltu _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ => True
  | _ => True

/-- Partial v2 dispatcher for RTYPE+Binary arms. -/
theorem zisk_riscv_compliant_program_bus_rtype_binary
    (env : OpEnvelope state m r_main) :
    env.exec_eq_rtype_binary := by
  cases env with
  | sub sub_input r1 r2 rd v bus pins providerTable providerRow h_component
      h_table_spec h_provider_row h_match_static h_lane_rd promises =>
    simp only [OpEnvelope.exec_eq_rtype_binary]
    exact ZiskFv.Equivalence.Sub.equiv_SUB
      state sub_input r1 r2 rd m providerTable providerRow r_main bus pins
      h_component h_table_spec h_provider_row h_match_static h_lane_rd promises
  | and and_input r1 r2 rd v bus pins providerTable providerRow h_component
      h_table_spec h_provider_row h_match_static h_lane_rd promises =>
    simp only [OpEnvelope.exec_eq_rtype_binary]
    exact ZiskFv.Equivalence.And.equiv_AND_of_static_table_row
      state and_input r1 r2 rd m providerTable providerRow r_main bus pins
      h_component h_table_spec h_provider_row h_match_static h_lane_rd promises
  | or or_input r1 r2 rd v bus pins providerTable providerRow h_component
      h_table_spec h_provider_row h_match_static h_lane_rd promises =>
    simp only [OpEnvelope.exec_eq_rtype_binary]
    exact ZiskFv.Equivalence.Or.equiv_OR_of_static_table_row
      state or_input r1 r2 rd m providerTable providerRow r_main bus pins
      h_component h_table_spec h_provider_row h_match_static h_lane_rd promises
  | xor xor_input r1 r2 rd v bus pins providerTable providerRow h_component
      h_table_spec h_provider_row h_match_static h_lane_rd promises =>
    simp only [OpEnvelope.exec_eq_rtype_binary]
    exact ZiskFv.Equivalence.Xor.equiv_XOR_of_static_table_row
      state xor_input r1 r2 rd m providerTable providerRow r_main bus pins
      h_component h_table_spec h_provider_row h_match_static h_lane_rd promises
  | slt slt_input r1 r2 rd v bus pins providerTable providerRow h_component
      h_table_spec h_provider_row h_match_static h_lane_rd promises =>
    simp only [OpEnvelope.exec_eq_rtype_binary]
    exact ZiskFv.Equivalence.Slt.equiv_SLT
      state slt_input r1 r2 rd m providerTable providerRow r_main bus pins
      h_component h_table_spec h_provider_row h_match_static h_lane_rd promises
  | sltu sltu_input r1 r2 rd v bus pins providerTable providerRow h_component
      h_table_spec h_provider_row h_match_static h_lane_rd promises =>
    simp only [OpEnvelope.exec_eq_rtype_binary]
    exact ZiskFv.Equivalence.Sltu.equiv_SLTU
      state sltu_input r1 r2 rd m providerTable providerRow r_main bus pins
      h_component h_table_spec h_provider_row h_match_static h_lane_rd promises
  | _ => trivial

end ZiskFv.Compliance
