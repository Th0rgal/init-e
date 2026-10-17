import InitECandidate.Runtime.RlpValidationWrapperCore
import InitECandidate.Runtime.ScratchMarkCall
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

theorem source_rlpValidation_wrapper : sourceFunctionBody Guest.guestFn_rlp_validate_items =
    .decCall (ofString "mark") .one (ofString "scratch_mark") []
      (.dec (ofString "e") .one (.const 0) rlpValidationWrapperCore) := by
  simp only [rlpValidationWrapperCore,sourceFunctionBody,InitECandidate.Proofs.FrontendCodecComputation.declToHOL_eq]
  rfl

/-- Complete original public validator function, including scratch mark,
normal/exception cleanup, declarations and scope restoration. -/
theorem evaluate_rlpValidation_wrapper_bounded {F : Type} (state : PanSemStateFiniteExact 64 F)
    (pointer length scratch frame : BitVec 64) (ceiling inputLimit : Nat)
    (pointerLocal : state.locals.lookup (ofString "p") = some (.val (.word pointer)))
    (lengthLocal : state.locals.lookup (ofString "len") = some (.val (.word length)))
    (noWrap : pointer.toNat + length.toNat < 2^64) (lengthBound : length.toNat ≤ inputLimit)
    (limitBound : inputLimit + 9 < 2^64)
    (scratchGlobal : state.globals.lookup (ofString "scratch_ptr") = some (.val (.word scratch)))
    (frameGlobal : state.globals.lookup (ofString "frame_mem_ptr") = some (.val (.word frame)))
    (code : state.code = originalRuntimeCode) (orderedFrame : frame ≤ scratch) (framePositive : 0 < frame.toNat)
    (scratchBelow : scratch.toNat ≤ ceiling)
    (arena : ∀ address : BitVec 64, frame.toNat ≤ address.toNat → address.toNat < ceiling → state.memaddrs address)
    (budget : (2 * length.toNat + 1) * 15 + 4 ≤ state.clock) :
    let evaluated := evaluateHOLFiniteState state (sourceFunctionBody Guest.guestFn_rlp_validate_items)
    state.clock ≤ evaluated.2.clock + ((2 * length.toNat + 1) * 15 + 4) ∧ evaluated.2.clock ≤ state.clock ∧
      evaluated.1 ≠ some .timeOut ∧ evaluated.1 ≠ none := by
  obtain ⟨ready,_,clock,memory,globals,locals,readyCode,domain,_,declaration⟩ :=
    evaluate_scratchMark_call_and_declaration state scratch code scratchGlobal (by omega)
  let marked := setVarHOLFinite (ofString "mark") (.val (.word scratch)) ready
  let entered := setVarHOLFinite (ofString "e") (.val (.word 0)) marked
  have localFrame : ∀ name, name ≠ ofString "mark" → name ≠ ofString "e" → entered.locals.lookup name = state.locals.lookup name := by
    intro name notMark notError
    simp [entered,marked,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,Ne.symm notMark,Ne.symm notError,locals]
  have atMark : entered.locals.lookup (ofString "mark") = some (.val (.word scratch)) := by
    simp [entered,marked,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,show ofString "e" ≠ ofString "mark" by decide]
  have atScratch : entered.globals.lookup (ofString "scratch_ptr") = some (.val (.word scratch)) := by
    change ready.globals.lookup _ = _
    rw [globals]; exact scratchGlobal
  have atFrame : entered.globals.lookup (ofString "frame_mem_ptr") = some (.val (.word frame)) := by
    change ready.globals.lookup _ = _
    rw [globals]; exact frameGlobal
  have enteredArena : ∀ address : BitVec 64, frame.toNat ≤ address.toNat → address.toNat < ceiling → entered.memaddrs address := by
    simpa only [entered,marked,setVarHOLFinite,domain] using arena
  have core := evaluate_rlpValidation_wrapper_core_bounded entered pointer length scratch frame ceiling inputLimit scratch atMark
    ((localFrame _ (by decide) (by decide)).trans pointerLocal) ((localFrame _ (by decide) (by decide)).trans lengthLocal)
    noWrap lengthBound limitBound atScratch atFrame (readyCode.trans code) orderedFrame framePositive scratchBelow enteredArena
    (by change (2 * length.toNat + 1) * 15 + 3 ≤ ready.clock; omega)
  cases run : evaluateHOLFiniteState state (sourceFunctionBody Guest.guestFn_rlp_validate_items) with
  | mk result post =>
    have exposed := run
    rw [source_rlpValidation_wrapper,declaration] at exposed
    change (let output := evaluateHOLFiniteState marked (.dec (ofString "e") .one (.const 0) rlpValidationWrapperCore);
      (output.1,{output.2 with locals := HolFiniteMapExact.resVarEq output.2.locals (ofString "mark",state.locals.lookup (ofString "mark"))})) = (result,post) at exposed
    cases errorRun : evaluateHOLFiniteState marked (.dec (ofString "e") .one (.const 0) rlpValidationWrapperCore) with
    | mk innerResult innerPost =>
      rw [errorRun] at exposed
      have sameResult := (Prod.mk.inj exposed).1
      change innerResult = result at sameResult
      subst innerResult
      obtain ⟨output,coreRun,restored⟩ := evaluate_dec_word_result_scope marked innerPost (ofString "e") (.const 0) 0
        rlpValidationWrapperCore result (by rfl) errorRun
      change evaluateHOLFiniteState entered rlpValidationWrapperCore = (result,output) at coreRun
      rw [coreRun] at core
      have postClock : post.clock = output.clock := by
        rw [← (Prod.mk.inj exposed).2,restored]
      have enteredClock : entered.clock = ready.clock := rfl
      dsimp only at core ⊢
      exact ⟨by omega,by omega,core.2.2.1,core.2.2.2⟩

#print axioms evaluate_rlpValidation_wrapper_bounded
end InitECandidate.Runtime
