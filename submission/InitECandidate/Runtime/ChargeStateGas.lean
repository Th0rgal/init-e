import InitECandidate.Runtime.ChargeGas
import InitECandidate.Runtime.AddSat

namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

def stateGasDebit : ExpHOL 64 :=
  .op .sub [.var .local (ofString "sgl"), .var .local (ofString "amount")]
def stateGasEnough : ExpHOL 64 :=
  .cmp .notLower (.var .local (ofString "sgl")) (.var .local (ofString "amount"))
def stateGasSpillTail : ProgHOL 64 :=
  match sourceFunctionBody Guest.guestFn_charge_state_gas with
  | .dec _ _ _ (.dec _ _ _ (.seq _ tail)) => tail
  | _ => .skip

theorem source_chargeStateGas_body : sourceFunctionBody Guest.guestFn_charge_state_gas =
    .dec (ofString "sgl") .one (fundingLoad 72)
      (.dec (ofString "gl") .one (fundingLoad 64)
        (.seq (.ite stateGasEnough
          (.seq (.store (fundingAddress 72) stateGasDebit) (.return (.const 0))) .skip)
          stateGasSpillTail)) := by cbv

noncomputable def stateGasCoveredPost {σ : Type} (state : PanSemStateFiniteExact 64 σ)
    (frame stateLeft left amount : BitVec 64) : PanSemStateFiniteExact 64 σ :=
  let entry := setVarHOLFinite (ofString "gl") (.val (.word left))
    (setVarHOLFinite (ofString "sgl") (.val (.word stateLeft)) state)
  let written := emptyLocalsHOLFinite (sourceWriteWord entry (frame + 72) (stateLeft - amount))
  let inner := { written with locals := (HolFiniteMapExact.resVarEq written.locals
    (ofString "gl", state.locals.lookup (ofString "gl"))) }
  { inner with locals := (HolFiniteMapExact.resVarEq inner.locals
    (ofString "sgl", state.locals.lookup (ofString "sgl"))) }

/-- A covered state-gas charge returns before the add_sat call, including at
clock zero. Only the state-gas cell changes. -/
theorem evaluate_chargeStateGas_covered {σ : Type} (state : PanSemStateFiniteExact 64 σ)
    (frame stateLeft left amount : BitVec 64)
    (hFrame : state.globals.lookup (ofString "ev") = some (.val (.word frame)))
    (hAmount : state.locals.lookup (ofString "amount") = some (.val (.word amount)))
    (stateDomain : state.memaddrs (frame + 72))
    (leftDomain : state.memaddrs (frame + 64))
    (stateMemory : state.memory (frame + 72) = .word stateLeft)
    (leftMemory : state.memory (frame + 64) = .word left)
    (enough : amount ≤ stateLeft) :
    evaluateHOLFiniteState state (sourceFunctionBody Guest.guestFn_charge_state_gas) =
      (some (.returned (.val (.word 0))), stateGasCoveredPost state frame stateLeft left amount) := by
  classical
  let outer := setVarHOLFinite (ofString "sgl") (.val (.word stateLeft)) state
  let entry := setVarHOLFinite (ofString "gl") (.val (.word left)) outer
  let written := sourceWriteWord entry (frame + 72) (stateLeft - amount)
  have names : ofString "gl" ≠ ofString "sgl" ∧ ofString "sgl" ≠ ofString "amount" ∧
      ofString "gl" ≠ ofString "amount" := by decide_cbv
  have eState : entry.locals.lookup (ofString "sgl") = some (.val (.word stateLeft)) := by
    simp [entry, outer, setVarHOLFinite, FUPDATE, names.1]
  have eAmount : entry.locals.lookup (ofString "amount") = some (.val (.word amount)) := by
    simpa [entry, outer, setVarHOLFinite, FUPDATE, names.2.1, names.2.2] using hAmount
  have debit : evaluateHOLFiniteState entry (.store (fundingAddress 72) stateGasDebit) =
      (none, written) := by
    apply evaluate_store_word
    · exact eval_fundingAddress entry frame 72 hFrame
    · simp [stateGasDebit, evalHOLExact, evalListHOLExact, toExact, eState, eAmount,
        valueIsWord, valueWord, wordOpHOL, wordOp]
    · exact stateDomain
  have finish : evaluateHOLFiniteState written (.return (.const 0)) =
      (some (.returned (.val (.word 0))), emptyLocalsHOLFinite written) := by
    simp [evaluateHOLFiniteState_return, evalHOLExact, shapeOfHOLExact]
  have guard : evaluateHOLFiniteState entry
      (.ite stateGasEnough (.seq (.store (fundingAddress 72) stateGasDebit)
        (.return (.const 0))) .skip) =
      (some (.returned (.val (.word 0))), emptyLocalsHOLFinite written) := by
    rw [evaluateHOLFiniteState_ite]
    have natEnough := BitVec.le_def.mp enough
    simpa [stateGasEnough, evalHOLExact, toExact, eState, eAmount,
      Flapjack.Compiler.Encoders.Asm.wordCmpHOL, BitVec.lt_def, Nat.not_lt.mpr natEnough]
      using evaluate_seq_none debit finish
  have body := evaluate_seq_some (second := stateGasSpillTail) guard
  rw [source_chargeStateGas_body, evaluateHOLFiniteState_dec_total]
  dsimp only
  rw [eval_fundingLoad state frame 72 stateLeft hFrame stateDomain stateMemory]
  simp only [shapeOfHOLExact, shapeEqHOL]
  rw [show setVarHOLFinite (ofString "sgl") (.val (.word stateLeft)) state = outer from rfl]
  rw [evaluateHOLFiniteState_dec_total]
  dsimp only
  rw [eval_fundingLoad outer frame 64 left hFrame leftDomain leftMemory]
  simp only [shapeOfHOLExact, shapeEqHOL]
  rw [show setVarHOLFinite (ofString "gl") (.val (.word left)) outer = entry from rfl]
  rw [body]
  simp [stateGasCoveredPost, outer, entry, written, setVarHOLFinite, FUPDATE, names.1,
    Ne.symm names.1]

theorem stateGasCoveredPost_funding {σ : Type} (state : PanSemStateFiniteExact 64 σ)
    (frame stateLeft left amount : BitVec 64) (funding : GasFunding)
    (memory : HasGasFunding state frame funding) :
    HasGasFunding (stateGasCoveredPost state frame stateLeft left amount) frame funding := by
  unfold HasGasFunding
  simpa [HasGasFunding, stateGasCoveredPost, emptyLocalsHOLFinite, sourceWriteWord, setVarHOLFinite] using memory

/-- Once the state-only branch is excluded, the saturating guard proves that
its remainder is an ordinary, non-wrapping debit of regular gas. -/
theorem stateGas_spill_enough (stateLeft left amount : BitVec 64)
    (short : stateLeft.toNat < amount.toNat)
    (covered : amount ≤ wordAddSat stateLeft left) :
    amount - stateLeft ≤ left ∧
      (amount - stateLeft).toNat = amount.toNat - stateLeft.toNat ∧
      0 < (amount - stateLeft).toNat := by
  have guard := (wordAddSat_enough stateLeft left amount).mp covered
  have noUnderflow : stateLeft ≤ amount := BitVec.le_def.mpr (by omega)
  have debit := gasDebit_toNat amount stateLeft noUnderflow
  refine ⟨BitVec.le_def.mpr ?_, debit, ?_⟩
  · rw [debit]; omega
  · rw [debit]; omega

theorem stateGas_spill_preserves_potential (funding : GasFunding)
    (stateLeft amount : BitVec 64)
    (budget : funding.potential ≤ 200000000)
    (short : stateLeft.toNat < amount.toNat)
    (covered : amount ≤ wordAddSat stateLeft funding.left) :
    (funding.spill (amount - stateLeft)).potential = funding.potential := by
  exact funding.spill_potential _ budget (stateGas_spill_enough stateLeft funding.left amount short covered).1

end InitECandidate.Runtime
#print axioms InitECandidate.Runtime.evaluate_chargeStateGas_covered

#print axioms InitECandidate.Runtime.stateGas_spill_preserves_potential
