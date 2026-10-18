import InitECandidate.Runtime.BlobHashesProgress
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

theorem blobHashes_copy_normal_other_local {F : Type} (state post : PanSemStateFiniteExact 64 F)
    (index count array : BitVec 64)
    (indexLocal : state.locals.lookup (ofString "i") = some (.val (.word index)))
    (listLocal : state.locals.lookup (ofString "lst") = some (.rStruct [.val (.word array),.val (.word count)]))
    (key : MlS) (different : key ≠ ofString "i")
    (run : evaluateHOLFiniteState state blobHashesCopyAndAdvance = (none,post)) :
    post.locals.lookup key = state.locals.lookup key := by
  let arguments : List (ExpHOL 64) :=
    [.op .add [.var .local (ofString "buf"),.panop .mul [.var .local (ofString "i"),.const 32]],
     .var .local (ofString "h"),.const 32]
  rw [source_blobHashes_copy_and_advance,evaluateHOLFiniteState_seq_line780] at run
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
      have advanced : evaluateHOLFiniteState middle (.assign .local (ofString "i")
          (.op .add [.var .local (ofString "i"),.const 1])) =
          (none,setVarHOLFinite (ofString "i") (.val (.word (index + 1))) middle) := by
        simp [evaluateHOLFiniteState_assign,evalHOLExact,evalListHOLExact,atIndex,
          lookupKvarHOLExact,isValidValueHOLExact,shapeOfHOLExact,shapeEqHOL,setKvarHOLFinite,wordOpHOL,wordOp,valueIsWord,valueWord]
      have postEq := (Prod.mk.inj (run.symm.trans advanced)).2
      rw [postEq]
      simp [setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,Ne.symm different,locals]

theorem blobHashes_step_normal_buffer_local {F : Type} (state post : PanSemStateFiniteExact 64 F)
    (index count array buffer : BitVec 64)
    (indexLocal : state.locals.lookup (ofString "i") = some (.val (.word index)))
    (listLocal : state.locals.lookup (ofString "lst") = some (.rStruct [.val (.word array),.val (.word count)]))
    (bufferLocal : state.locals.lookup (ofString "buf") = some (.val (.word buffer)))
    (run : evaluateHOLFiniteState state blobHashesStep = (none,post)) :
    post.locals.lookup (ofString "buf") = some (.val (.word buffer)) := by
  have step : blobHashesStep = .decCall (ofString "h") .one (ofString "tx_fixed_bytes")
      [.rfield 0 (.var .local (ofString "lst")),.var .local (ofString "i"),.const 32] blobHashesCopyAndAdvance := by
    rw [blobHashesCopyAndAdvance,source_blobHashes_step]
  rw [step] at run
  obtain ⟨value,ready,output,locals,tail,restored⟩ := evaluate_decCall_unconditional_normal_scope state post _ _ _ _ _ run
  let entered := setVarHOLFinite (ofString "h") value ready
  have atIndex : entered.locals.lookup (ofString "i") = some (.val (.word index)) := by
    simpa [entered,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,locals,
      show ofString "h" ≠ ofString "i" by decide] using indexLocal
  have atList : entered.locals.lookup (ofString "lst") = some (.rStruct [.val (.word array),.val (.word count)]) := by
    simpa [entered,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,locals,
      show ofString "h" ≠ ofString "lst" by decide] using listLocal
  have frame := blobHashes_copy_normal_other_local entered output index count array atIndex atList (ofString "buf") (by decide) tail
  rw [restored]
  change (HolFiniteMapExact.resVarEq output.locals (ofString "h",state.locals.lookup (ofString "h"))).lookup (ofString "buf") = _
  rw [restore_other_local _ _ _ _ (by decide),frame]
  simpa [entered,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,locals,
    show ofString "h" ≠ ofString "buf" by decide] using bufferLocal

#print axioms blobHashes_copy_normal_other_local
#print axioms blobHashes_step_normal_buffer_local
end InitECandidate.Runtime
