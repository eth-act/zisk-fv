import ZiskFv.Completeness.Rv64im.SailDecode.Domain

/-!
# Actual Sail ISA guards and a concrete M-enabled state

Source boundary: `flake.lock` pins sail-riscv to
`04e595954b2af7fa9e18f2519e4ae4bba72b2701`. Its
`model/extensions/M/mext_insts.sail:13-14` defines the M guard by `misa[M]`
and derives Zmmul from standalone hart support OR the M guard. The standalone
support comes from `model/core/extensions.sail:37,130`; the extraction config
`nix/sail-riscv-zisk-rv64d.json:92-94,158-160` selects M=true, Zmmul=false.
MISA's M field is bit 12 (`model/core/sys_regs.sail:48-78`). These are the
actual generated declarations in `LeanRV64D/Types.lean:351-352,550-551`,
`Extensions.lean:637-661`, and `Defs.lean:1748`.

The separate Sail fork input is pinned to
`46acc966ff845b11361c854d59d82a47bd42b487` (parent
`277470b2ab472af8064e1295be5573845239c96b`), but `flake.nix` does not apply
that input to `nix/sail-lean-tree.nix`: that recipe inherits nixpkgs's Sail
compiler. The proofs below depend on the actual imported generated Lean,
not a claim that the otherwise pinned compiler input generated it.

The constructor writes genuine typed `Register.misa` storage. It establishes
constructibility of this decode/encode domain, not boot reachability or a
fully initialized executable machine: the other registers of `default` are
absent. No boot/runtime ISA promise or additional domain premise is introduced.
-/

namespace ZiskFv.Completeness.SailDecode

/-- The pinned hart supports the full M extension. -/
theorem hartSupports_m_true :
    LeanRV64D.Functions.hartSupports extension.Ext_M = true := by
  simp only [LeanRV64D.Functions.hartSupports]

/-- Standalone multiply-only support remains disabled in the pinned hart. -/
theorem hartSupports_zmmul_false :
    LeanRV64D.Functions.hartSupports extension.Ext_Zmmul = false := by
  simp only [LeanRV64D.Functions.hartSupports]

/-- Zmmul's *enabled* guard includes M, despite standalone Zmmul support being false. -/
theorem currentlyEnabled_zmmul_eq_m :
    LeanRV64D.Functions.currentlyEnabled extension.Ext_Zmmul =
      LeanRV64D.Functions.currentlyEnabled extension.Ext_M := by
  conv_lhs => unfold LeanRV64D.Functions.currentlyEnabled
  change (LeanRV64D.Functions.currentlyEnabled extension.Ext_M >>= fun enabled =>
    pure (LeanRV64D.Functions.hartSupports extension.Ext_Zmmul || enabled)) =
      LeanRV64D.Functions.currentlyEnabled extension.Ext_M
  rw [hartSupports_zmmul_false]
  simp
  funext state
  cases Sail.readReg Register.misa state <;> rfl

/-- Consumers derive Zmmul enablement from the actual M-only domain. -/
theorem zmmul_enabled_of_isaExtensionsEnabled (state : SailState)
    (h : IsaExtensionsEnabled state) :
    LeanRV64D.Functions.currentlyEnabled extension.Ext_Zmmul state =
      EStateM.Result.ok true state := by
  rw [currentlyEnabled_zmmul_eq_m]
  exact h

/-- The actual M guard is faithful in both directions to a successful MISA read
whose M bit is set. In particular, absent register storage cannot enable M. -/
theorem currentlyEnabled_m_iff_misa (state : SailState) :
    LeanRV64D.Functions.currentlyEnabled extension.Ext_M state =
        EStateM.Result.ok true state ↔
      ∃ misa : BitVec 64,
        Sail.readReg Register.misa state = EStateM.Result.ok misa state ∧
          LeanRV64D.Functions._get_Misa_M misa = 1#1 := by
  rw [LeanRV64D.Functions.currentlyEnabled]
  change ((Sail.readReg Register.misa >>= fun value =>
    pure (LeanRV64D.Functions.hartSupports extension.Ext_M &&
      (LeanRV64D.Functions._get_Misa_M value == 1#1))) state = _) ↔ _
  rw [hartSupports_m_true]
  cases h_misa : state.regs.get? Register.misa <;>
    simp [Sail.readReg, PreSail.readReg, bind, h_misa]

/-- Read-to-guard direction, with no independent enablement assumption. -/
theorem currentlyEnabled_m_of_misa (state : SailState) (misa : BitVec 64)
    (h_misa : Sail.readReg Register.misa state = EStateM.Result.ok misa state)
    (h_m : LeanRV64D.Functions._get_Misa_M misa = 1#1) :
    LeanRV64D.Functions.currentlyEnabled extension.Ext_M state =
      EStateM.Result.ok true state :=
  (currentlyEnabled_m_iff_misa state).2 ⟨misa, h_misa, h_m⟩

/-- The proof-facing domain neither adds to nor loses the generated MISA guard. -/
theorem isaExtensionsEnabled_iff_misa (state : SailState) :
    IsaExtensionsEnabled state ↔
      ∃ misa : BitVec 64,
        Sail.readReg Register.misa state = EStateM.Result.ok misa state ∧
          LeanRV64D.Functions._get_Misa_M misa = 1#1 :=
  currentlyEnabled_m_iff_misa state

/-- Replace only MISA with a value whose M bit (bit 12) is set. This is a domain
witness, not a claim that this value is a reset CSR or the result of a CSR instruction. -/
def withMEnabled (state : SailState) : SailState :=
  write_reg_state state Register.misa 4096#64

/-- The state update is exactly Sail's typed register-write operation. -/
theorem withMEnabled_write_misa (state : SailState) :
    Sail.writeReg Register.misa 4096#64 state =
      EStateM.Result.ok PUnit.unit (withMEnabled state) :=
  writeReg_state_success

/-- The MISA value is really present in dependent register storage and readable. -/
theorem withMEnabled_read_misa (state : SailState) :
    Sail.readReg Register.misa (withMEnabled state) =
      EStateM.Result.ok 4096#64 (withMEnabled state) := by
  apply readReg_succ
  exact writeReg_read_same state

theorem withMEnabled_m (state : SailState) :
    LeanRV64D.Functions.currentlyEnabled extension.Ext_M (withMEnabled state) =
      EStateM.Result.ok true (withMEnabled state) := by
  apply currentlyEnabled_m_of_misa _ 4096#64
  · exact withMEnabled_read_misa state
  · decide

theorem withMEnabled_isaExtensionsEnabled (state : SailState) :
    IsaExtensionsEnabled (withMEnabled state) :=
  withMEnabled_m state

theorem withMEnabled_zmmul (state : SailState) :
    LeanRV64D.Functions.currentlyEnabled extension.Ext_Zmmul (withMEnabled state) =
      EStateM.Result.ok true (withMEnabled state) :=
  zmmul_enabled_of_isaExtensionsEnabled _ (withMEnabled_isaExtensionsEnabled state)

/-- A closed, concrete Sail state with actual MISA storage, used by the
state-aware encoder/classifier constructibility witnesses. -/
def mEnabledState : SailState := withMEnabled default

theorem mEnabledState_isaExtensionsEnabled : IsaExtensionsEnabled mEnabledState :=
  withMEnabled_isaExtensionsEnabled default

/-- An actual Sail write constructs the witness, and its derived Zmmul guard is true. -/
theorem mEnabledState_constructible :
    Sail.writeReg Register.misa 4096#64 (default : SailState) =
        EStateM.Result.ok PUnit.unit mEnabledState ∧
      LeanRV64D.Functions.currentlyEnabled extension.Ext_Zmmul mEnabledState =
        EStateM.Result.ok true mEnabledState :=
  ⟨withMEnabled_write_misa default, withMEnabled_zmmul default⟩

end ZiskFv.Completeness.SailDecode
