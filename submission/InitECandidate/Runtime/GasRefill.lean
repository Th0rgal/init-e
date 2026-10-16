import InitECandidate.Runtime.FrameHalt

namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

def refillCredit : ExpHOL 64 := .op .add [fundingLoad 64, fundingLoad 192]
def refillMessageGas : ExpHOL 64 :=
  .load .one (.op .add [.var .local (ofString "msg"), .const 48])
def refillStores : ProgHOL 64 :=
  .seq (.store (fundingAddress 64) refillCredit)
    (.seq (.store (fundingAddress 72) refillMessageGas)
      (.seq (.store (fundingAddress 192) (.const 0)) (.return (.const 0))))
theorem source_gasRefill_body : sourceFunctionBody Guest.guestFn_refill_frame_state_gas =
    .dec (ofString "msg") .one (fundingLoad 112) refillStores := by cbv

noncomputable def refillPost {σ : Type} (state : PanSemStateFiniteExact 64 σ)
    (frame left spilled gas : BitVec 64) : PanSemStateFiniteExact 64 σ :=
  emptyLocalsHOLFinite (sourceWriteWord (sourceWriteWord
    (sourceWriteWord state (frame + 64) (left + spilled)) (frame + 72) gas) (frame + 192) 0)

/-- Refill reads the message after its first store. Non-aliasing of that read
is explicit, rather than inferred from a frame layout that is not yet proved. -/
theorem evaluate_refillStores {σ : Type} (state : PanSemStateFiniteExact 64 σ)
    (frame msg gas left spilled : BitVec 64)
    (hFrame : state.globals.lookup (ofString "ev") = some (.val (.word frame)))
    (hMsg : state.locals.lookup (ofString "msg") = some (.val (.word msg)))
    (leftDomain : state.memaddrs (frame + 64))
    (spillDomain : state.memaddrs (frame + 192))
    (stateDomain : state.memaddrs (frame + 72))
    (msgDomain : state.memaddrs (msg + 48))
    (leftMemory : state.memory (frame + 64) = .word left)
    (spillMemory : state.memory (frame + 192) = .word spilled)
    (msgMemory : state.memory (msg + 48) = .word gas)
    (separate : msg + 48 ≠ frame + 64) :
    evaluateHOLFiniteState state refillStores =
      (some (.returned (.val (.word 0))), refillPost state frame left spilled gas) := by
  classical
  let one := sourceWriteWord state (frame + 64) (left + spilled)
  let two := sourceWriteWord one (frame + 72) gas
  let three := sourceWriteWord two (frame + 192) 0
  have first : evaluateHOLFiniteState state (.store (fundingAddress 64) refillCredit) =
      (none, one) := by
    apply evaluate_store_word
    · exact eval_fundingAddress state frame 64 hFrame
    · unfold refillCredit
      simp only [evalHOLExact, evalListHOLExact]
      rw [eval_fundingLoad state frame 64 left hFrame leftDomain leftMemory,
        eval_fundingLoad state frame 192 spilled hFrame spillDomain spillMemory]
      simp [valueIsWord, valueWord, wordOpHOL, wordOp]
    · exact leftDomain
  have second : evaluateHOLFiniteState one (.store (fundingAddress 72) refillMessageGas) =
      (none, two) := by
    apply evaluate_store_word
    · exact eval_fundingAddress one frame 72 hFrame
    · simp [refillMessageGas, evalHOLExact, evalListHOLExact, toExact, one, sourceWriteWord,
        hMsg, wordOpHOL, wordOp, valueIsWord, valueWord, isWfShapeExactHOL,
        memLoadHOLExact]
      exact ⟨msgDomain, (if_neg separate).trans msgMemory⟩
    · exact stateDomain
  have third : evaluateHOLFiniteState two (.store (fundingAddress 192) (.const 0)) =
      (none, three) := by
    apply evaluate_store_word
    · exact eval_fundingAddress two frame 192 hFrame
    · rfl
    · exact spillDomain
  have finish : evaluateHOLFiniteState three (.return (.const 0)) =
      (some (.returned (.val (.word 0))), emptyLocalsHOLFinite three) := by
    simp [evaluateHOLFiniteState_return, evalHOLExact, shapeOfHOLExact]
  exact evaluate_seq_none first (evaluate_seq_none second (evaluate_seq_none third finish))

theorem refillPost_funding {σ : Type} (state : PanSemStateFiniteExact 64 σ)
    (frame gas : BitVec 64) (funding : GasFunding)
    (memory : HasGasFunding state frame funding) :
    HasGasFunding (refillPost state frame funding.left funding.spilled gas)
      frame (funding.repay funding.spilled) := by
  unfold HasGasFunding
  simp [refillPost, sourceWriteWord, emptyLocalsHOLFinite, GasFunding.repay]
  exact memory.2.1

/-- Full refill execution repays all spill without consuming source clock. -/
theorem gasRefill_preserves_funding {σ : Type} (state : PanSemStateFiniteExact 64 σ)
    (frame msg gas : BitVec 64) (funding : GasFunding)
    (hFrame : state.globals.lookup (ofString "ev") = some (.val (.word frame)))
    (leftDomain : state.memaddrs (frame + 64))
    (spillDomain : state.memaddrs (frame + 192))
    (stateDomain : state.memaddrs (frame + 72))
    (pointerDomain : state.memaddrs (frame + 112))
    (msgDomain : state.memaddrs (msg + 48))
    (pointerMemory : state.memory (frame + 112) = .word msg)
    (msgMemory : state.memory (msg + 48) = .word gas)
    (separate : msg + 48 ≠ frame + 64)
    (memory : HasGasFunding state frame funding)
    (budget : funding.potential ≤ 200000000) :
    ∃ post, evaluateHOLFiniteState state
        (sourceFunctionBody Guest.guestFn_refill_frame_state_gas) =
        (some (.returned (.val (.word 0))), post) ∧
      HasGasFunding post frame (funding.repay funding.spilled) ∧
      (funding.repay funding.spilled).potential = funding.potential ∧
      post.clock = state.clock := by
  classical
  let entry := setVarHOLFinite (ofString "msg") (.val (.word msg)) state
  let bodyPost := refillPost entry frame funding.left funding.spilled gas
  let post := { bodyPost with locals := (HolFiniteMapExact.resVarEq bodyPost.locals
    (ofString "msg", state.locals.lookup (ofString "msg"))) }
  have entryMsg : entry.locals.lookup (ofString "msg") = some (.val (.word msg)) := by
    simp [entry, setVarHOLFinite, FUPDATE]
  have body := evaluate_refillStores entry frame msg gas funding.left funding.spilled hFrame
    entryMsg leftDomain spillDomain stateDomain msgDomain memory.1 memory.2.2 msgMemory separate
  refine ⟨post, ?_, ?_, funding.repay_potential funding.spilled budget (BitVec.le_refl _), rfl⟩
  · rw [source_gasRefill_body, evaluateHOLFiniteState_dec_total]
    dsimp only
    rw [eval_fundingLoad state frame 112 msg hFrame pointerDomain pointerMemory]
    simp only [shapeOfHOLExact, shapeEqHOL]
    change (let output := evaluateHOLFiniteState entry refillStores;
      (output.1, { output.2 with locals := (HolFiniteMapExact.resVarEq output.2.locals
        (ofString "msg", state.locals.lookup (ofString "msg"))) })) = _
    rw [body]
  · exact refillPost_funding entry frame gas funding memory

end InitECandidate.Runtime
#print axioms InitECandidate.Runtime.evaluate_refillStores

#print axioms InitECandidate.Runtime.gasRefill_preserves_funding
