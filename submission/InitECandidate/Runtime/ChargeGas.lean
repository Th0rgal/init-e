import InitECandidate.Runtime.FrameHalt

namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- The used-counter addition stored by the actual charge_gas helper. -/
def chargeGasUsedExpression : ExpHOL 64 :=
  .op .add [fundingLoad 184, .var .local (ofString "amount")]

def chargeGasTail : ProgHOL 64 :=
  .seq (.ite chargeGasCheck (.raise (ofString "EvmErr") (.const 4)) .skip)
    (.seq (.store (fundingAddress 64) gasDebitExpression)
      (.seq (.store (fundingAddress 184) chargeGasUsedExpression) (.return (.const 0))))

theorem source_chargeGas_body : sourceFunctionBody Guest.guestFn_charge_gas =
    .dec (ofString "gl") .one (fundingLoad 64) chargeGasTail := by cbv

noncomputable def chargeGasPost (state : PanSemStateFiniteExact 64 Guest.HostMemory)
    (frame left used amount : BitVec 64) : PanSemStateFiniteExact 64 Guest.HostMemory :=
  let entry := setVarHOLFinite (ofString "gl") (.val (.word left)) state
  let post := emptyLocalsHOLFinite (sourceWriteWord
    (sourceWriteWord entry (frame + 64) (left - amount)) (frame + 184) (used + amount))
  { post with locals := (HolFiniteMapExact.resVarEq post.locals
      (ofString "gl", state.locals.lookup (ofString "gl"))) }

theorem eval_chargeGasUsedExpression (state : PanSemStateFiniteExact 64 Guest.HostMemory)
    (frame used amount : BitVec 64)
    (hFrame : state.globals.lookup (ofString "ev") = some (.val (.word frame)))
    (hAmount : state.locals.lookup (ofString "amount") = some (.val (.word amount)))
    (domain : state.memaddrs (frame + 184))
    (memory : state.memory (frame + 184) = .word used) :
    @evalHOLExact 64 Guest.HostMemory _ state.toExact
      (fun address => Classical.propDecidable (state.memaddrs address)) chargeGasUsedExpression =
      some (.val (.word (used + amount))) := by
  classical
  unfold chargeGasUsedExpression
  simp only [evalHOLExact, evalListHOLExact]
  rw [eval_fundingLoad state frame 184 used hFrame domain memory]
  simp [evalHOLExact, toExact, hAmount, valueIsWord, valueWord, wordOpHOL, wordOp]

/-- Complete successful execution of the authoritative charge_gas body.
Its memory and local-scope effects are explicit, at an arbitrary source clock. -/
theorem evaluate_source_chargeGas (state : PanSemStateFiniteExact 64 Guest.HostMemory)
    (frame left used amount : BitVec 64)
    (hFrame : state.globals.lookup (ofString "ev") = some (.val (.word frame)))
    (hAmount : state.locals.lookup (ofString "amount") = some (.val (.word amount)))
    (leftDomain : state.memaddrs (frame + 64))
    (usedDomain : state.memaddrs (frame + 184))
    (leftMemory : state.memory (frame + 64) = .word left)
    (usedMemory : state.memory (frame + 184) = .word used)
    (enough : amount ≤ left) :
    evaluateHOLFiniteState state (sourceFunctionBody Guest.guestFn_charge_gas) =
      (some (.returned (.val (.word 0))), chargeGasPost state frame left used amount) := by
  classical
  let entry := setVarHOLFinite (ofString "gl") (.val (.word left)) state
  let one := sourceWriteWord entry (frame + 64) (left - amount)
  let two := sourceWriteWord one (frame + 184) (used + amount)
  have names : ofString "amount" ≠ ofString "gl" := by decide_cbv
  have entryLeft : entry.locals.lookup (ofString "gl") = some (.val (.word left)) := by
    simp [entry, setVarHOLFinite, HolFiniteMapExact.lookup_update_pointwise, FUPDATE]
  have entryAmount : entry.locals.lookup (ofString "amount") = some (.val (.word amount)) := by
    simpa [entry, setVarHOLFinite, HolFiniteMapExact.lookup_update_pointwise, FUPDATE, names, Ne.symm names] using hAmount
  have lower : ¬ left.toNat < amount.toNat := by
    have bound := BitVec.le_def.mp enough
    omega
  have guard : evaluateHOLFiniteState entry
      (.ite chargeGasCheck (.raise (ofString "EvmErr") (.const 4)) .skip) = (none, entry) := by
    rw [evaluateHOLFiniteState_ite, eval_chargeGasCheck entry left amount entryLeft entryAmount]
    simp [lower]
  have debit : evaluateHOLFiniteState entry (.store (fundingAddress 64) gasDebitExpression) =
      (none, one) := evaluate_store_word entry (frame + 64) (left - amount) _ _
        (eval_fundingAddress entry frame 64 hFrame)
        (eval_gasDebitExpression entry left amount entryLeft entryAmount) leftDomain
  have usedUnchanged : one.memory (frame + 184) = .word used := by
    simpa [one, sourceWriteWord, entry, setVarHOLFinite] using usedMemory
  have spent : evaluateHOLFiniteState one (.store (fundingAddress 184) chargeGasUsedExpression) =
      (none, two) := evaluate_store_word one (frame + 184) (used + amount) _ _
        (eval_fundingAddress one frame 184 hFrame)
        (eval_chargeGasUsedExpression one frame used amount hFrame entryAmount usedDomain usedUnchanged)
        usedDomain
  have finish : evaluateHOLFiniteState two (.return (.const 0)) =
      (some (.returned (.val (.word 0))), emptyLocalsHOLFinite two) := by
    simp [evaluateHOLFiniteState_return, evalHOLExact, shapeOfHOLExact]
  have body : evaluateHOLFiniteState entry chargeGasTail =
      (some (.returned (.val (.word 0))), emptyLocalsHOLFinite two) :=
    evaluate_seq_none guard (evaluate_seq_none debit (evaluate_seq_none spent finish))
  rw [source_chargeGas_body, evaluateHOLFiniteState_dec_total]
  dsimp only
  rw [eval_fundingLoad state frame 64 left hFrame leftDomain leftMemory]
  simp only [shapeOfHOLExact, shapeEqHOL]
  change (let output := evaluateHOLFiniteState entry chargeGasTail;
    (output.1, { output.2 with locals := (HolFiniteMapExact.resVarEq output.2.locals
      (ofString "gl", state.locals.lookup (ofString "gl"))) })) = _
  rw [body]
  try rfl

theorem chargeGasPost_funding (state : PanSemStateFiniteExact 64 Guest.HostMemory)
    (frame amount : BitVec 64) (funding : GasFunding)
    (memory : HasGasFunding state frame funding) :
    HasGasFunding (chargeGasPost state frame funding.left funding.used amount)
      frame (funding.charge amount) := by
  unfold HasGasFunding
  simp [chargeGasPost, sourceWriteWord, setVarHOLFinite, emptyLocalsHOLFinite, GasFunding.charge]
  exact memory.2.2

/-- The successful source helper performs precisely the funding debit. The
post-state is the one computed by the real evaluator, including scope cleanup. -/
theorem chargeGas_preserves_funding (state : PanSemStateFiniteExact 64 Guest.HostMemory)
    (frame amount : BitVec 64) (funding : GasFunding)
    (hFrame : state.globals.lookup (ofString "ev") = some (.val (.word frame)))
    (hAmount : state.locals.lookup (ofString "amount") = some (.val (.word amount)))
    (leftDomain : state.memaddrs (frame + 64))
    (usedDomain : state.memaddrs (frame + 184))
    (memory : HasGasFunding state frame funding)
    (budget : funding.potential ≤ 200000000) (enough : amount ≤ funding.left) :
    ∃ post, evaluateHOLFiniteState state (sourceFunctionBody Guest.guestFn_charge_gas) =
        (some (.returned (.val (.word 0))), post) ∧
      HasGasFunding post frame (funding.charge amount) ∧
      (funding.charge amount).potential = funding.potential ∧ post.clock = state.clock := by
  refine ⟨chargeGasPost state frame funding.left funding.used amount, ?_, ?_, ?_, rfl⟩
  · exact evaluate_source_chargeGas state frame funding.left funding.used amount hFrame hAmount
      leftDomain usedDomain memory.1 memory.2.1 enough
  · exact chargeGasPost_funding state frame amount funding memory
  · exact funding.charge_potential amount budget enough

noncomputable def chargeGasFailurePost (state : PanSemStateFiniteExact 64 Guest.HostMemory)
    (left : BitVec 64) : PanSemStateFiniteExact 64 Guest.HostMemory :=
  let post := emptyLocalsHOLFinite (setVarHOLFinite (ofString "gl") (.val (.word left)) state)
  { post with locals := (HolFiniteMapExact.resVarEq post.locals
      (ofString "gl", state.locals.lookup (ofString "gl"))) }

theorem evaluate_seq_some {σ : Type} {state middle : PanSemStateFiniteExact 64 σ}
    {first second : ProgHOL 64} {result : PanSemResultExact 64}
    (one : evaluateHOLFiniteState state first = (some result, middle)) :
    evaluateHOLFiniteState state (.seq first second) = (some result, middle) := by
  rw [evaluateHOLFiniteState_seq]
  dsimp only
  rw [fixClockHOLFinite_evaluateState, one]

/-- Insufficient gas raises the actual language exception before either gas
cell is written. No assumption about the requested amount's size is needed. -/
theorem evaluate_source_chargeGas_outOfGas (state : PanSemStateFiniteExact 64 Guest.HostMemory)
    (frame left amount : BitVec 64)
    (hFrame : state.globals.lookup (ofString "ev") = some (.val (.word frame)))
    (hAmount : state.locals.lookup (ofString "amount") = some (.val (.word amount)))
    (exceptionShape : state.eshapes.lookup (ofString "EvmErr") = some .one)
    (leftDomain : state.memaddrs (frame + 64))
    (leftMemory : state.memory (frame + 64) = .word left)
    (insufficient : left.toNat < amount.toNat) :
    evaluateHOLFiniteState state (sourceFunctionBody Guest.guestFn_charge_gas) =
      (some (.exception (ofString "EvmErr") (.val (.word 4))), chargeGasFailurePost state left) := by
  classical
  let entry := setVarHOLFinite (ofString "gl") (.val (.word left)) state
  have names : ofString "amount" ≠ ofString "gl" := by decide_cbv
  have entryLeft : entry.locals.lookup (ofString "gl") = some (.val (.word left)) := by
    simp [entry, setVarHOLFinite, FUPDATE]
  have entryAmount : entry.locals.lookup (ofString "amount") = some (.val (.word amount)) := by
    simpa [entry, setVarHOLFinite, FUPDATE, names, Ne.symm names] using hAmount
  have guard : evaluateHOLFiniteState entry
      (.ite chargeGasCheck (.raise (ofString "EvmErr") (.const 4)) .skip) =
      (some (.exception (ofString "EvmErr") (.val (.word 4))), emptyLocalsHOLFinite entry) := by
    rw [evaluateHOLFiniteState_ite, eval_chargeGasCheck entry left amount entryLeft entryAmount]
    simp only [if_pos insufficient]
    simp [evaluateHOLFiniteState_raise, evalHOLExact, shapeOfHOLExact,
      entry, setVarHOLFinite, exceptionShape]
  have body : evaluateHOLFiniteState entry chargeGasTail =
      (some (.exception (ofString "EvmErr") (.val (.word 4))), emptyLocalsHOLFinite entry) :=
    evaluate_seq_some guard
  rw [source_chargeGas_body, evaluateHOLFiniteState_dec_total]
  dsimp only
  rw [eval_fundingLoad state frame 64 left hFrame leftDomain leftMemory]
  simp only [shapeOfHOLExact, shapeEqHOL]
  change (let output := evaluateHOLFiniteState entry chargeGasTail;
    (output.1, { output.2 with locals := (HolFiniteMapExact.resVarEq output.2.locals
      (ofString "gl", state.locals.lookup (ofString "gl"))) })) = _
  rw [body]
  try rfl

theorem chargeGasFailurePost_preserves_funding
    (state : PanSemStateFiniteExact 64 Guest.HostMemory) (frame left : BitVec 64)
    (funding : GasFunding) (memory : HasGasFunding state frame funding) :
    HasGasFunding (chargeGasFailurePost state left) frame funding := memory

end InitECandidate.Runtime

#print axioms InitECandidate.Runtime.evaluate_source_chargeGas

#print axioms InitECandidate.Runtime.chargeGas_preserves_funding

#print axioms InitECandidate.Runtime.evaluate_source_chargeGas_outOfGas
