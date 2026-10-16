import InitECandidate.Runtime.MinCall
import InitECandidate.Runtime.FrameHalt

namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

def refundCredit : ExpHOL 64 :=
  .op .add [fundingLoad 64, .var .local (ofString "from_gl")]
def refundSpilled : ExpHOL 64 :=
  .op .sub [.var .local (ofString "spilled"), .var .local (ofString "from_gl")]
def refundStateCredit : ExpHOL 64 :=
  .op .add [fundingLoad 72,
    .op .sub [.var .local (ofString "amount"), .var .local (ofString "from_gl")]]
def refundStores : ProgHOL 64 :=
  .seq (.store (fundingAddress 64) refundCredit)
    (.seq (.store (fundingAddress 192) refundSpilled)
      (.seq (.store (fundingAddress 72) refundStateCredit) (.return (.const 0))))
def refundCall : ProgHOL 64 :=
  .decCall (ofString "from_gl") .one (ofString "min")
    [.var .local (ofString "amount"), .var .local (ofString "spilled")] refundStores

theorem source_gasRefund_body : sourceFunctionBody Guest.guestFn_credit_state_gas_refund =
    .dec (ofString "spilled") .one (fundingLoad 192) refundCall := by cbv

noncomputable def refundStoresPost {σ : Type} (state : PanSemStateFiniteExact 64 σ)
    (frame left spilled stateLeft amount credit : BitVec 64) : PanSemStateFiniteExact 64 σ :=
  emptyLocalsHOLFinite (sourceWriteWord (sourceWriteWord
    (sourceWriteWord state (frame + 64) (left + credit))
    (frame + 192) (spilled - credit)) (frame + 72) (stateLeft + (amount - credit)))

/-- The refund stores execute without further calls or clock consumption. -/
theorem evaluate_refundStores {σ : Type} (state : PanSemStateFiniteExact 64 σ)
    (frame left spilled stateLeft amount credit : BitVec 64)
    (hFrame : state.globals.lookup (ofString "ev") = some (.val (.word frame)))
    (hAmount : state.locals.lookup (ofString "amount") = some (.val (.word amount)))
    (hSpilled : state.locals.lookup (ofString "spilled") = some (.val (.word spilled)))
    (hCredit : state.locals.lookup (ofString "from_gl") = some (.val (.word credit)))
    (leftDomain : state.memaddrs (frame + 64))
    (spillDomain : state.memaddrs (frame + 192))
    (stateDomain : state.memaddrs (frame + 72))
    (leftMemory : state.memory (frame + 64) = .word left)
    (stateMemory : state.memory (frame + 72) = .word stateLeft) :
    evaluateHOLFiniteState state refundStores =
      (some (.returned (.val (.word 0))),
        refundStoresPost state frame left spilled stateLeft amount credit) := by
  classical
  let one := sourceWriteWord state (frame + 64) (left + credit)
  let two := sourceWriteWord one (frame + 192) (spilled - credit)
  let three := sourceWriteWord two (frame + 72) (stateLeft + (amount - credit))
  have first : evaluateHOLFiniteState state (.store (fundingAddress 64) refundCredit) =
      (none, one) := by
    apply evaluate_store_word
    · exact eval_fundingAddress state frame 64 hFrame
    · unfold refundCredit
      simp only [evalHOLExact, evalListHOLExact]
      rw [eval_fundingLoad state frame 64 left hFrame leftDomain leftMemory]
      simp [evalHOLExact, toExact, hCredit, valueIsWord, valueWord, wordOpHOL, wordOp]
    · exact leftDomain
  have second : evaluateHOLFiniteState one (.store (fundingAddress 192) refundSpilled) =
      (none, two) := by
    apply evaluate_store_word
    · exact eval_fundingAddress one frame 192 hFrame
    · simp [refundSpilled, evalHOLExact, evalListHOLExact, toExact, one, sourceWriteWord,
        hSpilled, hCredit, valueIsWord, valueWord, wordOpHOL, wordOp]
    · exact spillDomain
  have unchanged : two.memory (frame + 72) = .word stateLeft := by
    simpa [two, one, sourceWriteWord] using stateMemory
  have third : evaluateHOLFiniteState two (.store (fundingAddress 72) refundStateCredit) =
      (none, three) := by
    apply evaluate_store_word
    · exact eval_fundingAddress two frame 72 hFrame
    · unfold refundStateCredit
      simp only [evalHOLExact, evalListHOLExact]
      rw [eval_fundingLoad two frame 72 stateLeft hFrame stateDomain unchanged]
      simp [evalHOLExact, toExact, two, one, sourceWriteWord, hAmount, hCredit,
        valueIsWord, valueWord, wordOpHOL, wordOp]
    · exact stateDomain
  have finish : evaluateHOLFiniteState three (.return (.const 0)) =
      (some (.returned (.val (.word 0))), emptyLocalsHOLFinite three) := by
    simp [evaluateHOLFiniteState_return, evalHOLExact, shapeOfHOLExact]
  exact evaluate_seq_none first (evaluate_seq_none second (evaluate_seq_none third finish))

theorem refundStoresPost_funding {σ : Type} (state : PanSemStateFiniteExact 64 σ)
    (frame stateLeft amount credit : BitVec 64) (funding : GasFunding)
    (memory : HasGasFunding state frame funding) :
    HasGasFunding (refundStoresPost state frame funding.left funding.spilled stateLeft amount credit)
      frame (funding.repay credit) := by
  unfold HasGasFunding
  simp [refundStoresPost, sourceWriteWord, emptyLocalsHOLFinite, GasFunding.repay]
  exact memory.2.1

/-- Complete source execution of capped refund, including the min call.
The state-gas counter may wrap; the regular funding invariant does not. -/
theorem gasRefund_preserves_funding {σ : Type} (state : PanSemStateFiniteExact 64 σ)
    (frame stateLeft amount : BitVec 64) (funding : GasFunding)
    (hFrame : state.globals.lookup (ofString "ev") = some (.val (.word frame)))
    (hAmount : state.locals.lookup (ofString "amount") = some (.val (.word amount)))
    (installed : state.code.lookup (ofString "min") = some minCodeEntry)
    (clock : state.clock ≠ 0)
    (leftDomain : state.memaddrs (frame + 64))
    (spillDomain : state.memaddrs (frame + 192))
    (stateDomain : state.memaddrs (frame + 72))
    (memory : HasGasFunding state frame funding)
    (stateMemory : state.memory (frame + 72) = .word stateLeft)
    (budget : funding.potential ≤ 200000000) :
    ∃ post, evaluateHOLFiniteState state
        (sourceFunctionBody Guest.guestFn_credit_state_gas_refund) =
        (some (.returned (.val (.word 0))), post) ∧
      HasGasFunding post frame (funding.repay (wordMin amount funding.spilled)) ∧
      (funding.repay (wordMin amount funding.spilled)).potential = funding.potential ∧
      post.clock = state.clock - 1 := by
  classical
  let entry := setVarHOLFinite (ofString "spilled") (.val (.word funding.spilled)) state
  let next := setVarHOLFinite (ofString "from_gl")
    (.val (.word (wordMin amount funding.spilled))) { entry with clock := entry.clock - 1 }
  let storesPost := refundStoresPost next frame funding.left funding.spilled stateLeft amount
    (wordMin amount funding.spilled)
  let callPost := { storesPost with locals := (HolFiniteMapExact.resVarEq storesPost.locals
    (ofString "from_gl", entry.locals.lookup (ofString "from_gl"))) }
  let post := { callPost with locals := (HolFiniteMapExact.resVarEq callPost.locals
    (ofString "spilled", state.locals.lookup (ofString "spilled"))) }
  have distinct : ofString "spilled" ≠ ofString "amount" ∧
      ofString "from_gl" ≠ ofString "amount" ∧ ofString "from_gl" ≠ ofString "spilled" := by decide_cbv
  have eAmount : entry.locals.lookup (ofString "amount") = some (.val (.word amount)) := by
    simpa [entry, setVarHOLFinite, FUPDATE, distinct.1] using hAmount
  have eSpilled : entry.locals.lookup (ofString "spilled") = some (.val (.word funding.spilled)) := by
    simp [entry, setVarHOLFinite, FUPDATE]
  have nAmount : next.locals.lookup (ofString "amount") = some (.val (.word amount)) := by
    simpa [next, setVarHOLFinite, FUPDATE, distinct.2.1] using eAmount
  have nSpilled : next.locals.lookup (ofString "spilled") = some (.val (.word funding.spilled)) := by
    simpa [next, setVarHOLFinite, FUPDATE, distinct.2.2] using eSpilled
  have nCredit : next.locals.lookup (ofString "from_gl") =
      some (.val (.word (wordMin amount funding.spilled))) := by
    simp [next, setVarHOLFinite, FUPDATE]
  have args : evalListHOLFinite entry
      (h := fun address => Classical.propDecidable (entry.memaddrs address))
      [.var .local (ofString "amount"), .var .local (ofString "spilled")] =
      some [.val (.word amount), .val (.word funding.spilled)] := by
    simp [evalListHOLFinite, evalListHOLExact, evalHOLExact, toExact, eAmount, eSpilled]
  have stores := evaluate_refundStores next frame funding.left funding.spilled stateLeft amount
    (wordMin amount funding.spilled) hFrame nAmount nSpilled nCredit
    leftDomain spillDomain stateDomain memory.1 stateMemory
  have call : evaluateHOLFiniteState entry refundCall =
      (some (.returned (.val (.word 0))), callPost) := by
    unfold refundCall
    rw [evaluate_min_decCall entry _ _ _ amount funding.spilled installed args clock]
    change (let output := evaluateHOLFiniteState next refundStores;
      (output.1, { output.2 with locals := (HolFiniteMapExact.resVarEq output.2.locals
        (ofString "from_gl", entry.locals.lookup (ofString "from_gl"))) })) = _
    rw [stores]
  refine ⟨post, ?_, ?_, funding.capped_refund amount budget, rfl⟩
  · rw [source_gasRefund_body, evaluateHOLFiniteState_dec_total]
    dsimp only
    rw [eval_fundingLoad state frame 192 funding.spilled hFrame spillDomain memory.2.2]
    simp only [shapeOfHOLExact, shapeEqHOL]
    change (let output := evaluateHOLFiniteState entry refundCall;
      (output.1, { output.2 with locals := (HolFiniteMapExact.resVarEq output.2.locals
        (ofString "spilled", state.locals.lookup (ofString "spilled"))) })) = _
    rw [call]
  · exact refundStoresPost_funding next frame stateLeft amount _ funding memory

end InitECandidate.Runtime
#print axioms InitECandidate.Runtime.evaluate_refundStores

#print axioms InitECandidate.Runtime.gasRefund_preserves_funding
