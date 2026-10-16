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

def stateSpillDebit : ExpHOL 64 :=
  .op .sub [.var .local (ofString "gl"), .var .local (ofString "rem")]
def stateSpillAdd : ExpHOL 64 :=
  .op .add [fundingLoad 192, .var .local (ofString "rem")]
def stateSpillStores : ProgHOL 64 :=
  .seq (.store (fundingAddress 72) (.const 0))
    (.seq (.store (fundingAddress 64) stateSpillDebit)
      (.seq (.store (fundingAddress 192) stateSpillAdd) (.return (.const 0))))

theorem source_stateSpill_stores :
    (match stateGasSpillTail with
     | .decCall _ _ _ _ (.seq (.ite _ (.dec _ _ _ stores) _) _) => stores
     | _ => .skip) = stateSpillStores := by cbv

noncomputable def stateSpillPost {σ : Type} (state : PanSemStateFiniteExact 64 σ)
    (frame left spilled rem : BitVec 64) : PanSemStateFiniteExact 64 σ :=
  emptyLocalsHOLFinite (sourceWriteWord (sourceWriteWord
    (sourceWriteWord state (frame + 72) 0) (frame + 64) (left - rem))
    (frame + 192) (spilled + rem))

theorem evaluate_stateSpillStores {σ : Type} (state : PanSemStateFiniteExact 64 σ)
    (frame left spilled rem : BitVec 64)
    (hFrame : state.globals.lookup (ofString "ev") = some (.val (.word frame)))
    (hLeft : state.locals.lookup (ofString "gl") = some (.val (.word left)))
    (hRem : state.locals.lookup (ofString "rem") = some (.val (.word rem)))
    (stateDomain : state.memaddrs (frame + 72))
    (leftDomain : state.memaddrs (frame + 64))
    (spillDomain : state.memaddrs (frame + 192))
    (spillMemory : state.memory (frame + 192) = .word spilled) :
    evaluateHOLFiniteState state stateSpillStores =
      (some (.returned (.val (.word 0))), stateSpillPost state frame left spilled rem) := by
  classical
  let one := sourceWriteWord state (frame + 72) 0
  let two := sourceWriteWord one (frame + 64) (left - rem)
  let three := sourceWriteWord two (frame + 192) (spilled + rem)
  have first : evaluateHOLFiniteState state (.store (fundingAddress 72) (.const 0)) =
      (none, one) := evaluate_store_word state _ _ _ _
        (eval_fundingAddress state frame 72 hFrame) rfl stateDomain
  have second : evaluateHOLFiniteState one (.store (fundingAddress 64) stateSpillDebit) =
      (none, two) := by
    apply evaluate_store_word
    · exact eval_fundingAddress one frame 64 hFrame
    · simp [stateSpillDebit, evalHOLExact, evalListHOLExact, toExact, one, sourceWriteWord,
        hLeft, hRem, valueIsWord, valueWord, wordOpHOL, wordOp]
    · exact leftDomain
  have unchanged : two.memory (frame + 192) = .word spilled := by
    simpa [two, one, sourceWriteWord] using spillMemory
  have third : evaluateHOLFiniteState two (.store (fundingAddress 192) stateSpillAdd) =
      (none, three) := by
    apply evaluate_store_word
    · exact eval_fundingAddress two frame 192 hFrame
    · unfold stateSpillAdd
      simp only [evalHOLExact, evalListHOLExact]
      rw [eval_fundingLoad two frame 192 spilled hFrame spillDomain unchanged]
      simp [toExact, two, one, sourceWriteWord, hRem, valueIsWord, valueWord, wordOpHOL, wordOp]
    · exact spillDomain
  have finish : evaluateHOLFiniteState three (.return (.const 0)) =
      (some (.returned (.val (.word 0))), emptyLocalsHOLFinite three) := by
    simp [evaluateHOLFiniteState_return, evalHOLExact, shapeOfHOLExact]
  exact evaluate_seq_none first (evaluate_seq_none second (evaluate_seq_none third finish))

theorem stateSpillPost_funding {σ : Type} (state : PanSemStateFiniteExact 64 σ)
    (frame rem : BitVec 64) (funding : GasFunding)
    (memory : HasGasFunding state frame funding) :
    HasGasFunding (stateSpillPost state frame funding.left funding.spilled rem)
      frame (funding.spill rem) := by
  unfold HasGasFunding
  simp [stateSpillPost, sourceWriteWord, emptyLocalsHOLFinite, GasFunding.spill]
  exact memory.2.1

def stateSpillBranch : ProgHOL 64 :=
  .dec (ofString "rem") .one
    (.op .sub [.var .local (ofString "amount"), .var .local (ofString "sgl")]) stateSpillStores

theorem source_stateSpill_branch :
    (match stateGasSpillTail with
     | .decCall _ _ _ _ (.seq (.ite _ branch _) _) => branch
     | _ => .skip) = stateSpillBranch := by cbv

/-- The actual spill branch computes the remainder and restores its scope.
The saturation guard is sufficient for its funding conservation premise. -/
theorem evaluate_stateSpillBranch {σ : Type} (state : PanSemStateFiniteExact 64 σ)
    (frame stateLeft amount : BitVec 64) (funding : GasFunding)
    (hFrame : state.globals.lookup (ofString "ev") = some (.val (.word frame)))
    (hLeft : state.locals.lookup (ofString "gl") = some (.val (.word funding.left)))
    (hState : state.locals.lookup (ofString "sgl") = some (.val (.word stateLeft)))
    (hAmount : state.locals.lookup (ofString "amount") = some (.val (.word amount)))
    (stateDomain : state.memaddrs (frame + 72))
    (leftDomain : state.memaddrs (frame + 64))
    (spillDomain : state.memaddrs (frame + 192))
    (memory : HasGasFunding state frame funding)
    (budget : funding.potential ≤ 200000000)
    (short : stateLeft.toNat < amount.toNat)
    (covered : amount ≤ wordAddSat stateLeft funding.left) :
    ∃ post, evaluateHOLFiniteState state stateSpillBranch =
        (some (.returned (.val (.word 0))), post) ∧
      HasGasFunding post frame (funding.spill (amount - stateLeft)) ∧
      (funding.spill (amount - stateLeft)).potential = funding.potential ∧
      post.clock = state.clock := by
  classical
  let entry := setVarHOLFinite (ofString "rem") (.val (.word (amount - stateLeft))) state
  let written := stateSpillPost entry frame funding.left funding.spilled (amount - stateLeft)
  let post := { written with locals := (HolFiniteMapExact.resVarEq written.locals
    (ofString "rem", state.locals.lookup (ofString "rem"))) }
  have names : ofString "rem" ≠ ofString "gl" := by decide_cbv
  have eLeft : entry.locals.lookup (ofString "gl") = some (.val (.word funding.left)) := by
    simpa [entry, setVarHOLFinite, FUPDATE, names] using hLeft
  have eRem : entry.locals.lookup (ofString "rem") = some (.val (.word (amount - stateLeft))) := by
    simp [entry, setVarHOLFinite, FUPDATE]
  have body := evaluate_stateSpillStores entry frame funding.left funding.spilled (amount - stateLeft)
    hFrame eLeft eRem stateDomain leftDomain spillDomain memory.2.2
  refine ⟨post, ?_, stateSpillPost_funding entry frame (amount - stateLeft) funding memory,
    stateGas_spill_preserves_potential funding stateLeft amount budget short covered, rfl⟩
  rw [stateSpillBranch, evaluateHOLFiniteState_dec_total]
  have expression : @evalHOLExact 64 σ _ state.toExact
      (fun address => Classical.propDecidable (state.memaddrs address))
      (.op .sub [.var .local (ofString "amount"), .var .local (ofString "sgl")]) =
      some (.val (.word (amount - stateLeft))) := by
    simp [evalHOLExact, evalListHOLExact, toExact, hAmount, hState,
      valueIsWord, valueWord, wordOpHOL, wordOp]
  dsimp only
  rw [expression]
  simp only [shapeOfHOLExact, shapeEqHOL]
  rw [show setVarHOLFinite (ofString "rem") (.val (.word (amount - stateLeft))) state = entry from rfl]
  rw [body]
  rfl

def stateSpillGuard : ExpHOL 64 :=
  .cmp .notLower (.var .local (ofString "tot")) (.var .local (ofString "amount"))
def stateSpillContinuation : ProgHOL 64 :=
  .seq (.ite stateSpillGuard stateSpillBranch .skip)
    (.seq (.raise (ofString "EvmErr") (.const 4)) (.return (.const 0)))
theorem source_stateSpill_tail : stateGasSpillTail =
    .decCall (ofString "tot") .one (ofString "add_sat")
      [.var .local (ofString "sgl"), .var .local (ofString "gl")] stateSpillContinuation := by cbv

/-- The successful spill tail includes the authoritative add_sat call and
its comparison; the only clock cost is the helper call. -/
theorem evaluate_stateSpillTail {σ : Type} (state : PanSemStateFiniteExact 64 σ)
    (frame stateLeft amount : BitVec 64) (funding : GasFunding)
    (hFrame : state.globals.lookup (ofString "ev") = some (.val (.word frame)))
    (hLeft : state.locals.lookup (ofString "gl") = some (.val (.word funding.left)))
    (hState : state.locals.lookup (ofString "sgl") = some (.val (.word stateLeft)))
    (hAmount : state.locals.lookup (ofString "amount") = some (.val (.word amount)))
    (installed : state.code.lookup (ofString "add_sat") = some addSatCodeEntry)
    (clock : state.clock ≠ 0)
    (stateDomain : state.memaddrs (frame + 72))
    (leftDomain : state.memaddrs (frame + 64))
    (spillDomain : state.memaddrs (frame + 192))
    (memory : HasGasFunding state frame funding)
    (budget : funding.potential ≤ 200000000)
    (short : stateLeft.toNat < amount.toNat)
    (covered : amount ≤ wordAddSat stateLeft funding.left) :
    ∃ post, evaluateHOLFiniteState state stateGasSpillTail =
        (some (.returned (.val (.word 0))), post) ∧
      HasGasFunding post frame (funding.spill (amount - stateLeft)) ∧
      (funding.spill (amount - stateLeft)).potential = funding.potential ∧
      post.clock = state.clock - 1 := by
  classical
  let next := setVarHOLFinite (ofString "tot")
    (.val (.word (wordAddSat stateLeft funding.left))) { state with clock := state.clock - 1 }
  have names : ofString "tot" ≠ ofString "gl" ∧ ofString "tot" ≠ ofString "sgl" ∧
      ofString "tot" ≠ ofString "amount" := by decide_cbv
  have nLeft : next.locals.lookup (ofString "gl") = some (.val (.word funding.left)) := by
    simpa [next, setVarHOLFinite, FUPDATE, names.1] using hLeft
  have nState : next.locals.lookup (ofString "sgl") = some (.val (.word stateLeft)) := by
    simpa [next, setVarHOLFinite, FUPDATE, names.2.1] using hState
  have nAmount : next.locals.lookup (ofString "amount") = some (.val (.word amount)) := by
    simpa [next, setVarHOLFinite, FUPDATE, names.2.2] using hAmount
  have nTotal : next.locals.lookup (ofString "tot") =
      some (.val (.word (wordAddSat stateLeft funding.left))) := by
    simp [next, setVarHOLFinite, FUPDATE]
  obtain ⟨written, branch, funded, conserved, timing⟩ :=
    evaluate_stateSpillBranch next frame stateLeft amount funding hFrame nLeft nState nAmount
      stateDomain leftDomain spillDomain memory budget short covered
  have guard : evaluateHOLFiniteState next (.ite stateSpillGuard stateSpillBranch .skip) =
      (some (.returned (.val (.word 0))), written) := by
    rw [evaluateHOLFiniteState_ite]
    have natCovered := BitVec.le_def.mp covered
    simpa [stateSpillGuard, evalHOLExact, toExact, nTotal, nAmount,
      Flapjack.Compiler.Encoders.Asm.wordCmpHOL, BitVec.lt_def, Nat.not_lt.mpr natCovered]
      using branch
  have continuation : evaluateHOLFiniteState next stateSpillContinuation =
      (some (.returned (.val (.word 0))), written) := evaluate_seq_some guard
  have args : evalListHOLFinite state
      (h := fun address => Classical.propDecidable (state.memaddrs address))
      [.var .local (ofString "sgl"), .var .local (ofString "gl")] =
      some [.val (.word stateLeft), .val (.word funding.left)] := by
    simp [evalListHOLFinite, evalListHOLExact, evalHOLExact, toExact, hState, hLeft]
  let post := { written with locals := (HolFiniteMapExact.resVarEq written.locals
    (ofString "tot", state.locals.lookup (ofString "tot"))) }
  refine ⟨post, ?_, funded, conserved, timing⟩
  rw [source_stateSpill_tail, evaluate_addSat_decCall state _ _ _ stateLeft funding.left installed args clock]
  change (let output := evaluateHOLFiniteState next stateSpillContinuation;
    (output.1, { output.2 with locals := (HolFiniteMapExact.resVarEq output.2.locals
      (ofString "tot", state.locals.lookup (ofString "tot"))) })) = _
  rw [continuation]

theorem evaluate_chargeStateGas_spill {σ : Type} (state : PanSemStateFiniteExact 64 σ)
    (frame stateLeft amount : BitVec 64) (funding : GasFunding)
    (hFrame : state.globals.lookup (ofString "ev") = some (.val (.word frame)))
    (hAmount : state.locals.lookup (ofString "amount") = some (.val (.word amount)))
    (installed : state.code.lookup (ofString "add_sat") = some addSatCodeEntry)
    (clock : state.clock ≠ 0)
    (stateDomain : state.memaddrs (frame + 72))
    (leftDomain : state.memaddrs (frame + 64))
    (spillDomain : state.memaddrs (frame + 192))
    (stateMemory : state.memory (frame + 72) = .word stateLeft)
    (memory : HasGasFunding state frame funding)
    (budget : funding.potential ≤ 200000000)
    (short : stateLeft.toNat < amount.toNat)
    (covered : amount ≤ wordAddSat stateLeft funding.left) :
    ∃ post, evaluateHOLFiniteState state (sourceFunctionBody Guest.guestFn_charge_state_gas) =
        (some (.returned (.val (.word 0))), post) ∧
      HasGasFunding post frame (funding.spill (amount - stateLeft)) ∧
      (funding.spill (amount - stateLeft)).potential = funding.potential ∧
      post.clock = state.clock - 1 := by
  classical
  let outer := setVarHOLFinite (ofString "sgl") (.val (.word stateLeft)) state
  let entry := setVarHOLFinite (ofString "gl") (.val (.word funding.left)) outer
  have names : ofString "gl" ≠ ofString "sgl" ∧ ofString "sgl" ≠ ofString "amount" ∧
      ofString "gl" ≠ ofString "amount" := by decide_cbv
  have eState : entry.locals.lookup (ofString "sgl") = some (.val (.word stateLeft)) := by
    simp [entry, outer, setVarHOLFinite, FUPDATE, names.1]
  have eLeft : entry.locals.lookup (ofString "gl") = some (.val (.word funding.left)) := by
    simp [entry, setVarHOLFinite, FUPDATE]
  have eAmount : entry.locals.lookup (ofString "amount") = some (.val (.word amount)) := by
    simpa [entry, outer, setVarHOLFinite, FUPDATE, names.2.1, names.2.2] using hAmount
  obtain ⟨written, tail, funded, conserved, timing⟩ := evaluate_stateSpillTail entry frame
    stateLeft amount funding hFrame eLeft eState eAmount installed clock stateDomain leftDomain
    spillDomain memory budget short covered
  have guard : evaluateHOLFiniteState entry
      (.ite stateGasEnough (.seq (.store (fundingAddress 72) stateGasDebit)
        (.return (.const 0))) .skip) = (none, entry) := by
    rw [evaluateHOLFiniteState_ite]
    simp [stateGasEnough, evalHOLExact, toExact, eState, eAmount,
      Flapjack.Compiler.Encoders.Asm.wordCmpHOL, BitVec.lt_def, short]
  have body := evaluate_seq_none guard tail
  let inner := { written with locals := (HolFiniteMapExact.resVarEq written.locals
    (ofString "gl", outer.locals.lookup (ofString "gl"))) }
  let post := { inner with locals := (HolFiniteMapExact.resVarEq inner.locals
    (ofString "sgl", state.locals.lookup (ofString "sgl"))) }
  refine ⟨post, ?_, funded, conserved, timing⟩
  rw [source_chargeStateGas_body, evaluateHOLFiniteState_dec_total]
  dsimp only
  rw [eval_fundingLoad state frame 72 stateLeft hFrame stateDomain stateMemory]
  simp only [shapeOfHOLExact, shapeEqHOL]
  rw [show setVarHOLFinite (ofString "sgl") (.val (.word stateLeft)) state = outer from rfl]
  rw [evaluateHOLFiniteState_dec_total]
  dsimp only
  rw [eval_fundingLoad outer frame 64 funding.left hFrame leftDomain memory.1]
  simp only [shapeOfHOLExact, shapeEqHOL]
  rw [show setVarHOLFinite (ofString "gl") (.val (.word funding.left)) outer = entry from rfl]
  rw [body]
  rfl

end InitECandidate.Runtime
#print axioms InitECandidate.Runtime.evaluate_chargeStateGas_covered

#print axioms InitECandidate.Runtime.stateGas_spill_preserves_potential

#print axioms InitECandidate.Runtime.evaluate_stateSpillStores

#print axioms InitECandidate.Runtime.evaluate_stateSpillBranch

#print axioms InitECandidate.Runtime.evaluate_stateSpillTail

#print axioms InitECandidate.Runtime.evaluate_chargeStateGas_spill
