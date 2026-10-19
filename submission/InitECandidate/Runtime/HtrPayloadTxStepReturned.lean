import InitECandidate.Runtime.HtrPayloadTxStepBound
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

theorem htrPayload_tx_step_normal {F : Type} (state post : PanSemStateFiniteExact 64 F)
    (array index pointer length roots heap : BitVec 64)
    (arrayLocal : state.locals.lookup (ofString "txs") = some (.val (.word array)))
    (indexLocal : state.locals.lookup (ofString "i") = some (.val (.word index)))
    (rootsLocal : state.locals.lookup (ofString "roots") = some (.val (.word roots)))
    (entry : RlpSliceEntry state array index pointer length)
    (atHeap : state.globals.lookup (ofString "heap_ptr") = some (.val (.word heap)))
    (code : state.code = originalRuntimeCode)
    (run : evaluateHOLFiniteState state htrPayloadTxStep = (none,post)) :
    post.globals = state.globals ∧
      post.locals.lookup (ofString "i") = some (.val (.word (index + (1#64)))) ∧
      ∀ key, key ≠ ofString "i" → post.locals.lookup key = state.locals.lookup key := by
  unfold htrPayloadTxStep at run
  rw [evaluateHOLFiniteState_seq_line780] at run
  cases callRun : evaluateHOLFiniteState state
      (.call (some (none,none)) (ofString "htr_pbytes") htrPayloadTxArguments) with
  | mk result middle =>
    rw [callRun] at run
    cases result with
    | some stopped => cases run
    | none =>
      have keep (key : MlS) : middle.locals.lookup key = state.locals.lookup key := by
        have kept := evaluate_avoidsLocal_flowing key
          (.call (some (none,none)) (ofString "htr_pbytes") htrPayloadTxArguments) rfl state
          (by rw [callRun]; exact Or.inl rfl)
        simpa only [callRun] using kept
      have globals := htrPbytes_call_normal_globals state middle htrPayloadTxArguments pointer length
        (roots + index * (32#64)) heap
        (htrPayload_tx_arguments state array index pointer length roots arrayLocal indexLocal rootsLocal entry)
        atHeap code callRun
      dsimp only at run
      rw [evaluate_increment_local middle (ofString "i") index ((keep _).trans indexLocal)] at run
      cases run
      refine ⟨globals,?_,?_⟩
      · simp [setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]
      · intro key different
        simp [setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,Ne.symm different,keep]

#print axioms htrPayload_tx_step_normal
end InitECandidate.Runtime
