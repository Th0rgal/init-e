import InitECandidate.Runtime.PanDecCallWatchedMemory
import InitECandidate.Runtime.WatchedMemoryComposition
import InitECandidate.Runtime.StoreBE32Memory
import InitECandidate.Runtime.PanSingleWordLookup
import InitECandidate.Runtime.PanDecCallTerminal
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
set_option maxRecDepth 100000

theorem bswap64_body_readOnly : readOnlyMemory (sourceFunctionBody Guest.guestFn_bswap64) = true := by
  rw [sourceFunctionBody_eq_structural]; rfl

/-- The optimized eight-byte store writes only its pointer word. The byte-swap
callee is read-only; no readable-memory or available-clock premise is needed. -/
theorem storeBE64_alignedBranch_memory {F : Type} (state : PanSemStateFiniteExact 64 F)
    (pointer value watched : BitVec 64)
    (atPointer : state.locals.lookup (ofString "p") = some (.val (.word pointer)))
    (atValue : state.locals.lookup (ofString "v") = some (.val (.word value)))
    (code : state.code = originalRuntimeCode) (separate : watched ≠ pointer) :
    (evaluateHOLFiniteState state storeBE64AlignedBranch).2.memory watched = state.memory watched := by
  have installed : state.code.lookup (ofString "bswap64") =
      some ([(ofString "x",.one)],sourceFunctionBody Guest.guestFn_bswap64,.one) := by
    rw [code]; exact originalRuntimeCode_bswap64_lookup
  have lookup := pan_single_word_lookup state.code.lookup (ofString "bswap64") (ofString "x")
    (sourceFunctionBody Guest.guestFn_bswap64) value installed
  unfold storeBE64AlignedBranch
  apply evaluate_decCall_watched_memory state _ _ _ _ _ [.val (.word value)] _ _ _ watched
    (by simp [evalListHOLFinite_eq_toExact,evalListHOLExact,evalHOLExact,atValue]) lookup bswap64_body_readOnly
  intro parsed ready shape locals memory
  have word : ∃ word : BitVec 64, parsed = .val (.word word) := by
    cases parsed with
    | val atom => cases atom with | word word => exact ⟨word,rfl⟩
    | rStruct fields => simp [shapeOfHOLExact,shapeEqHOL] at shape
    | nStruct name fields => simp [shapeOfHOLExact,shapeEqHOL] at shape
  obtain ⟨word,rfl⟩ := word
  let current := setVarHOLFinite (ofString "w") (.val (.word word)) ready
  change (evaluateHOLFiniteState current storeBE64AlignedTail).2.memory watched = ready.memory watched
  have pointerEval : @evalHOLExact 64 F _ current.toExact
      (fun a => Classical.propDecidable (current.memaddrs a)) (.var .local (ofString "p")) =
      some (.val (.word pointer)) := by
    simp (config := {decide := true}) [current,evalHOLExact,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,locals,atPointer]
  unfold storeBE64AlignedTail
  apply watched_memory_seq current _ _ watched
  · apply evaluate_wordStore_memory_frame current _ _ pointer watched pointerEval ?_ separate
    intro parsed found
    have equal : parsed = .val (.word word) := by
      simpa [current,evalHOLExact,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE] using found.symm
    exact ⟨word,equal⟩
  · intro next run
    exact congrFun (evaluate_readOnly_memory (.return (.const 0)) rfl next) watched

theorem storeBE64_alignedBranch_terminal {F : Type} (state : PanSemStateFiniteExact 64 F) :
    (evaluateHOLFiniteState state storeBE64AlignedBranch).1 ≠ none := by
  apply evaluate_decCall_terminal
  intro current
  unfold storeBE64AlignedTail
  rw [evaluateHOLFiniteState_seq_line780]
  cases run : evaluateHOLFiniteState current (.store (.var .local (ofString "p")) (.var .local (ofString "w"))) with
  | mk result post =>
    cases result with
    | none =>
      dsimp only
      rw [evaluateHOLFiniteState_return]
      simp [evalHOLExact,shapeOfHOLExact]
    | some result => simp

/-- An aligned pointer forces the optimized path of the unchanged source. -/
theorem storeBE64_aligned_body_memory {F : Type} (state : PanSemStateFiniteExact 64 F)
    (pointer value watched : BitVec 64)
    (atPointer : state.locals.lookup (ofString "p") = some (.val (.word pointer)))
    (atValue : state.locals.lookup (ofString "v") = some (.val (.word value)))
    (aligned : pointer.toNat % 8 = 0) (code : state.code = originalRuntimeCode)
    (separate : watched ≠ pointer) :
    (evaluateHOLFiniteState state (sourceFunctionBody Guest.guestFn_st_be64)).2.memory watched = state.memory watched := by
  have mask : pointer &&& (7 : BitVec 64) = 0 := by
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_and]
    change pointer.toNat &&& (2^3 - 1) = 0
    rw [Nat.and_two_pow_sub_one_eq_mod]
    exact aligned
  have loaded : @evalHOLExact 64 F _ state.toExact
      (fun a => Classical.propDecidable (state.memaddrs a))
      (.op .and [.var .local (ofString "p"),.const 7]) = some (.val (.word 0)) := by
    simp [evalHOLExact,evalListHOLExact,atPointer,wordOpHOL,wordOp,valueIsWord,valueWord]
    exact mask
  have guard : evaluateHOLFiniteState state storeBE64Guard = evaluateHOLFiniteState state storeBE64AlignedBranch := by
    unfold storeBE64Guard
    rw [evaluateHOLFiniteState_ite]
    rw [evalHOLExact,loaded]
    rfl
  rw [source_storeBE64_body]
  apply watched_memory_seq state _ _ watched
  · rw [guard]
    exact storeBE64_alignedBranch_memory state pointer value watched atPointer atValue code separate
  · intro next normal
    rw [guard] at normal
    have terminal := storeBE64_alignedBranch_terminal state
    rw [normal] at terminal
    exact False.elim (terminal rfl)

theorem storeBE64_aligned_call_normal_memory {F : Type} (state post : PanSemStateFiniteExact 64 F)
    (arguments : List (ExpHOL 64)) (pointer value watched : BitVec 64)
    (args : evalListHOLFinite state (h := fun a => Classical.propDecidable (state.memaddrs a)) arguments =
      some [.val (.word pointer),.val (.word value)]) (code : state.code = originalRuntimeCode)
    (aligned : pointer.toNat % 8 = 0) (separate : watched ≠ pointer)
    (run : evaluateHOLFiniteState state (.call (some (none,none)) (ofString "st_be64") arguments) = (none,post)) :
    post.memory watched = state.memory watched := by
  have installed : state.code.lookup (ofString "st_be64") =
      some ([(ofString "p",.one),(ofString "v",.one)],sourceFunctionBody Guest.guestFn_st_be64,.one) := by
    rw [code]; exact originalRuntimeCode_storeBE64_lookup
  have lookup := pan_two_word_lookup state.code.lookup (ofString "st_be64") (ofString "p") (ofString "v")
    (sourceFunctionBody Guest.guestFn_st_be64) pointer value (by decide) installed
  obtain ⟨returned,output,bodyRun,_,postEq⟩ := evaluate_discardCall_normal_result state post (ofString "st_be64")
    .one arguments _ _ _ args lookup run
  have frame := storeBE64_aligned_body_memory
    (callEntryStateHOLFinite state ((HolFiniteMapExact.empty.update (ofString "p",.val (.word pointer))).update
      (ofString "v",.val (.word value)))) pointer value watched
    (by simp (config := {decide := true}) [callEntryStateHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE])
    (by simp [callEntryStateHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]) aligned code separate
  rw [bodyRun] at frame
  rw [postEq]
  exact frame

#print axioms bswap64_body_readOnly
#print axioms storeBE64_alignedBranch_memory
#print axioms storeBE64_alignedBranch_terminal
#print axioms storeBE64_aligned_body_memory
#print axioms storeBE64_aligned_call_normal_memory
end InitECandidate.Runtime
