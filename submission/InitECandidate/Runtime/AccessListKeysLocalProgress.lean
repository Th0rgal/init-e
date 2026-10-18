import InitECandidate.Runtime.RlpSlicesAdvances
import InitECandidate.Runtime.PanDecCallUnconditionalNormalScope
import InitECandidate.Runtime.LocalScopeRestore
import InitECandidate.Runtime.AccessListSource
import InitECandidate.Runtime.DiscardCallSuccessLocals
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- Any normally completed original copy/advance suffix increments j and
preserves the slice pair, regardless of the callee's memory effects. -/
theorem access_keys_copy_normal_progress {F : Type} (state post : PanSemStateFiniteExact 64 F)
    (index count array : BitVec 64)
    (indexLocal : state.locals.lookup (ofString "j") = some (.val (.word index)))
    (listLocal : state.locals.lookup (ofString "slots") = some (.rStruct [.val (.word array),.val (.word count)]))
    (enabled : index.toNat < count.toNat)
    (run : evaluateHOLFiniteState state accessKeysCopy = (none,post)) :
    post.locals.lookup (ofString "j") = some (.val (.word (index + 1))) ∧
    post.locals.lookup (ofString "slots") = some (.rStruct [.val (.word array),.val (.word count)]) ∧
    (index + 1).toNat ≤ count.toNat ∧ count.toNat - (index + 1).toNat < count.toNat - index.toNat := by
  let arguments : List (ExpHOL 64) :=
    [.op .add [.var .local (ofString "keys"),.panop .mul [.var .local (ofString "j"),.const 32]],
     .var .local (ofString "k"),.const 32]
  rw [source_access_keys_copy,evaluateHOLFiniteState_seq_line780] at run
  cases copied : evaluateHOLFiniteState state (.call (some (none,none)) (ofString "memcpy") arguments) with
  | mk result middle =>
    dsimp only [arguments] at copied
    rw [copied] at run
    cases result with
    | some stopped => cases run
    | none =>
      have locals := evaluate_discard_call_success_locals state (ofString "memcpy") arguments (by rw [copied])
      rw [copied] at locals
      dsimp only at locals
      have atIndex := locals ▸ indexLocal
      have advanced : evaluateHOLFiniteState middle (.assign .local (ofString "j")
          (.op .add [.var .local (ofString "j"),.const 1])) =
          (none,setVarHOLFinite (ofString "j") (.val (.word (index + 1))) middle) := by
        simp [evaluateHOLFiniteState_assign,evalHOLExact,evalListHOLExact,atIndex,
          lookupKvarHOLExact,isValidValueHOLExact,shapeOfHOLExact,shapeEqHOL,setKvarHOLFinite,wordOpHOL,wordOp,valueIsWord,valueWord]
      have postEq := (Prod.mk.inj (run.symm.trans advanced)).2
      rw [postEq]
      have progress := rlpSlices_index_progress index count enabled
      refine ⟨?_,?_,progress.2⟩
      · simp [setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]
      · simpa [setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,locals,
          show ofString "j" ≠ ofString "slots" by decide] using listLocal

/-- Successful full access-list key iterations advance independently of the fixed-byte
callee's memory effects; its declaration restores caller locals. -/
theorem access_keys_step_normal_progress {F : Type} (state post : PanSemStateFiniteExact 64 F)
    (index count array : BitVec 64)
    (indexLocal : state.locals.lookup (ofString "j") = some (.val (.word index)))
    (listLocal : state.locals.lookup (ofString "slots") = some (.rStruct [.val (.word array),.val (.word count)]))
    (enabled : index.toNat < count.toNat)
    (run : evaluateHOLFiniteState state accessKeysStep = (none,post)) :
    post.locals.lookup (ofString "j") = some (.val (.word (index + 1))) ∧
    post.locals.lookup (ofString "slots") = some (.rStruct [.val (.word array),.val (.word count)]) ∧
    (index + 1).toNat ≤ count.toNat ∧ count.toNat - (index + 1).toNat < count.toNat - index.toNat := by
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
  obtain ⟨nextIndex,nextList,below,decreases⟩ := access_keys_copy_normal_progress entered output index count array atIndex atList enabled tail
  rw [restored]
  refine ⟨?_,?_,below,decreases⟩
  · change (HolFiniteMapExact.resVarEq output.locals (ofString "k",state.locals.lookup (ofString "k"))).lookup (ofString "j") = _
    rw [restore_other_local _ _ _ _ (by decide)]
    exact nextIndex
  · change (HolFiniteMapExact.resVarEq output.locals (ofString "k",state.locals.lookup (ofString "k"))).lookup (ofString "slots") = _
    rw [restore_other_local _ _ _ _ (by decide)]
    exact nextList

#print axioms access_keys_step_normal_progress

#print axioms access_keys_copy_normal_progress
end InitECandidate.Runtime
