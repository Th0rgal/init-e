import InitECandidate.Runtime.AccessListKeysBufferLocal
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

theorem access_keys_step_normal_other_local {F : Type} (state post : PanSemStateFiniteExact 64 F)
    (index count array : BitVec 64)
    (key : MlS) (different : key ≠ ofString "j") (notScoped : key ≠ ofString "k")
    (indexLocal : state.locals.lookup (ofString "j") = some (.val (.word index)))
    (listLocal : state.locals.lookup (ofString "slots") = some (.rStruct [.val (.word array),.val (.word count)]))
    (run : evaluateHOLFiniteState state accessKeysStep = (none,post)) :
    post.locals.lookup key = state.locals.lookup key := by
  have step : accessKeysStep = .decCall (ofString "k") .one (ofString "tx_fixed_bytes")
      [.rfield 0 (.var .local (ofString "slots")),.var .local (ofString "j"),.const 32] accessKeysCopy := by
    exact source_access_keys_step
  rw [step] at run
  obtain ⟨value,ready,output,locals,tail,restored⟩ := evaluate_decCall_unconditional_normal_scope state post _ _ _ _ _ run
  let entered := setVarHOLFinite (ofString "k") value ready
  have atIndex : entered.locals.lookup (ofString "j") = some (.val (.word index)) := by
    simpa [entered,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,locals,
      show ofString "k" ≠ ofString "j" by decide] using indexLocal
  have atList : entered.locals.lookup (ofString "slots") = some (.rStruct [.val (.word array),.val (.word count)]) := by
    simpa [entered,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,locals,
      show ofString "k" ≠ ofString "slots" by decide] using listLocal
  have frame := access_keys_copy_normal_other_local entered output index count array atIndex atList key different tail
  rw [restored]
  change (HolFiniteMapExact.resVarEq output.locals (ofString "k",state.locals.lookup (ofString "k"))).lookup key = _
  rw [restore_other_local _ _ _ _ notScoped,frame]
  simp [entered,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,locals,Ne.symm notScoped]

#print axioms access_keys_step_normal_other_local
end InitECandidate.Runtime
