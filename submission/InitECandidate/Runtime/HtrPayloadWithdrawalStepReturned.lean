import InitECandidate.Runtime.HtrPayloadWithdrawalStepBound
import InitECandidate.Runtime.HtrWithdrawalGlobals
import InitECandidate.Runtime.AvoidsLocalFrame
import InitECandidate.Runtime.LocalBoundLoop
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

theorem htrPayload_withdrawal_step_normal {F : Type} (state post : PanSemStateFiniteExact 64 F)
    (array index roots heap : BitVec 64)
    (arrayLocal : state.locals.lookup (ofString "wd") = some (.val (.word array)))
    (indexLocal : state.locals.lookup (ofString "i") = some (.val (.word index)))
    (rootsLocal : state.locals.lookup (ofString "roots") = some (.val (.word roots)))
    (atHeap : state.globals.lookup (ofString "heap_ptr") = some (.val (.word heap)))
    (code : state.code = originalRuntimeCode)
    (run : evaluateHOLFiniteState state htrPayloadWithdrawalStep = (none,post)) :
    post.globals = state.globals ∧
      post.locals.lookup (ofString "i") = some (.val (.word (index + (1#64)))) ∧
      ∀ key, key ≠ ofString "i" → post.locals.lookup key = state.locals.lookup key := by
  unfold htrPayloadWithdrawalStep at run
  rw [evaluateHOLFiniteState_seq_line780] at run
  cases callRun : evaluateHOLFiniteState state
      (.call (some (none,none)) (ofString "htr_withdrawal") htrPayloadWithdrawalArguments) with
  | mk result middle =>
    rw [callRun] at run
    cases result with
    | some stopped => cases run
    | none =>
      have keep (key : MlS) : middle.locals.lookup key = state.locals.lookup key := by
        have kept := evaluate_avoidsLocal_flowing key
          (.call (some (none,none)) (ofString "htr_withdrawal") htrPayloadWithdrawalArguments) rfl state
          (by rw [callRun]; exact Or.inl rfl)
        simpa only [callRun] using kept
      have globals := htrWithdrawal_call_normal_globals state middle htrPayloadWithdrawalArguments (array + index * (44#64))
        (roots + index * (32#64)) heap
        (htrPayload_withdrawal_arguments state array index roots arrayLocal indexLocal rootsLocal)
        atHeap code callRun
      dsimp only at run
      rw [evaluate_increment_local middle (ofString "i") index ((keep _).trans indexLocal)] at run
      cases run
      refine ⟨globals,?_,?_⟩
      · simp [setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]
      · intro key different
        simp [setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,Ne.symm different,keep]

#print axioms htrPayload_withdrawal_step_normal
end InitECandidate.Runtime
