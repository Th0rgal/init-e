import InitECandidate.Runtime.RlpUncheckedBodyFrame
import InitECandidate.Runtime.OriginalRlpUncheckedCode
import InitECandidate.Runtime.PanSingleWordLookup
import InitECandidate.Runtime.PanDecCallNormalWordFrame
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- Normal completion of the original unchecked declaration exposes a word
result and the actual continuation with caller locals restored. -/
theorem evaluate_rlpUnchecked_declaration_normal_frame {F : Type} (state post : PanSemStateFiniteExact 64 F)
    (name : MlS) (arguments : List (ExpHOL 64)) (continuation : ProgHOL 64) (pointer : BitVec 64)
    (args : evalListHOLFinite state (h := fun address => Classical.propDecidable (state.memaddrs address)) arguments =
      some [.val (.word pointer)])
    (code : state.code = originalRuntimeCode) (ticks : 11 ≤ state.clock)
    (run : evaluateHOLFiniteState state (.decCall name .one (ofString "rlp_item_total_unchecked") arguments continuation) = (none,post)) :
    ∃ (word : BitVec 64) (ready output : PanSemStateFiniteExact 64 F), ready.locals = state.locals ∧ ready.memory = state.memory ∧ ready.globals = state.globals ∧ ready.memaddrs = state.memaddrs ∧ ready.code = state.code ∧
      evaluateHOLFiniteState (setVarHOLFinite name (.val (.word word)) ready) continuation = (none,output) ∧
      post = {output with locals := HolFiniteMapExact.resVarEq output.locals (name,state.locals.lookup name)} := by
  have installed : state.code.lookup (ofString "rlp_item_total_unchecked") =
      some ([(ofString "p",.one)],sourceFunctionBody Guest.guestFn_rlp_item_total_unchecked,.one) := by
    rw [code]; exact originalRuntimeCode_rlpUnchecked_lookup
  have lookup := pan_single_word_lookup state.code.lookup (ofString "rlp_item_total_unchecked") (ofString "p")
    (sourceFunctionBody Guest.guestFn_rlp_item_total_unchecked) pointer installed
  let callee : HolFiniteMapExact MlS (ValueHOL 64) := HolFiniteMapExact.empty.update (ofString "p",.val (.word pointer))
  let entry := callEntryStateHOLFinite state callee
  have atPointer : entry.locals.lookup (ofString "p") = some (.val (.word pointer)) := by
    simp [entry,callee,callEntryStateHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]
  have bodyFrame : ∀ result output, evaluateHOLFiniteState entry (sourceFunctionBody Guest.guestFn_rlp_item_total_unchecked) =
      (result,output) → output.memory = state.memory ∧ output.globals = state.globals := by
    intro result output evaluated
    have frame := evaluate_rlpUnchecked_body_frame entry pointer atPointer code
      (by change 10 ≤ state.clock - 1; omega)
    rw [evaluated] at frame
    exact frame
  exact evaluate_decCall_one_normal_word_frame state post name (ofString "rlp_item_total_unchecked") arguments
    [.val (.word pointer)] (sourceFunctionBody Guest.guestFn_rlp_item_total_unchecked) continuation
    callee args lookup bodyFrame run

#print axioms evaluate_rlpUnchecked_declaration_normal_frame
end InitECandidate.Runtime
