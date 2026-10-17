import InitECandidate.Runtime.RlpSlicesBodyBound
import InitECandidate.Runtime.PanDecCallNormalReturnProperty
import InitECandidate.Runtime.PanDecCallNormalWord
import InitECandidate.Runtime.PanDecWordResultScope
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- The final scopes cannot fall through, even with malformed locals or no clock. -/
theorem evaluate_rlpSlices_initialized_terminal {F : Type} (state : PanSemStateFiniteExact 64 F) :
    (evaluateHOLFiniteState state rlpSlicesInitialized).1 ≠ none := by
  let initial := setVarHOLFinite (ofString "off") (.val (.word (0 : BitVec 64)))
    (setVarHOLFinite (ofString "i") (.val (.word (0 : BitVec 64))) state)
  have terminal : (evaluateHOLFiniteState initial rlpSlicesLoopAndReturn).1 ≠ none := by
    rw [source_rlpSlices_loop_and_return]
    exact evaluate_seq_terminal initial _ _ (fun current => evaluate_return_terminal current _)
  rw [source_rlpSlices_initialized,evaluateHOLFiniteState_dec_total]
  simp only [evalHOLExact,shapeOfHOLExact,shapeEqHOL,if_true]
  rw [evaluateHOLFiniteState_dec_total]
  simp only [evalHOLExact,shapeOfHOLExact,shapeEqHOL,if_true]
  cases run : evaluateHOLFiniteState initial rlpSlicesLoopAndReturn with
  | mk result post =>
    rw [run] at terminal
    exact terminal

/-- Allocation failures terminate, and successful allocations enter a terminal suffix. -/
theorem evaluate_rlpSlices_allocation_terminal {F : Type} (state : PanSemStateFiniteExact 64 F)
    (count : BitVec 64)
    (countLocal : state.locals.lookup (ofString "count") = some (.val (.word count)))
    (code : state.code = originalRuntimeCode) :
    (evaluateHOLFiniteState state rlpSlicesAllocation).1 ≠ none := by
  intro normal
  cases run : evaluateHOLFiniteState state rlpSlicesAllocation with
  | mk result post =>
    rw [run] at normal
    change result = none at normal
    subst result
    rw [source_rlpSlices_allocation] at run
    let argument : ExpHOL 64 := .panop .mul [.var .local (ofString "count"),.const 16]
    have args : evalListHOLFinite state (h := fun address => Classical.propDecidable (state.memaddrs address)) [argument] =
        some [.val (.word (count * 16))] := by
      simp [argument,evalListHOLFinite,evalListHOLExact,evalHOLExact,countLocal,panOpHOL,valueIsWord,valueWord]
    have installed : state.code.lookup (ofString "alloc") =
        some ([(ofString "n",.one)],sourceFunctionBody Guest.guestFn_alloc,.one) := by
      rw [code]; exact originalRuntimeCode_allocation_lookup
    have lookup := pan_single_word_lookup state.code.lookup (ofString "alloc") (ofString "n")
      (sourceFunctionBody Guest.guestFn_alloc) (count * 16) installed
    obtain ⟨value,ready,output,_,_,tail,_⟩ := evaluate_decCall_normal_return_property state post
      (ofString "arr") (ofString "alloc") .one .one [argument] [.val (.word (count * 16))]
      (sourceFunctionBody Guest.guestFn_alloc) rlpSlicesInitialized _ args lookup
      (fun _ => True) (by intro _ _ _; trivial) run
    have terminal := evaluate_rlpSlices_initialized_terminal (setVarHOLFinite (ofString "arr") value ready)
    rw [tail] at terminal
    exact terminal rfl

#print axioms evaluate_rlpSlices_initialized_terminal
#print axioms evaluate_rlpSlices_allocation_terminal
end InitECandidate.Runtime
