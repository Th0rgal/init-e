import InitECandidate.Runtime.WitnessExtensionSource
import InitECandidate.Runtime.PanStoreSequenceNormal
import InitECandidate.Runtime.LocalAssignNormalValue
import InitECandidate.Runtime.LoadOneRead
import InitECandidate.Runtime.WordStoreMemoryFrame
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

theorem witness_extension_sequence_normal_parts {F : Type} (s post : PanSemStateFiniteExact 64 F)
    (first tail : ProgHOL 64)
    (run : evaluateHOLFiniteState s (.seq first tail) = (none,post)) :
    ∃ middle, evaluateHOLFiniteState s first = (none,middle) ∧
      evaluateHOLFiniteState middle tail = (none,post) := by
  rw [evaluateHOLFiniteState_seq_line780] at run
  cases evaluated : evaluateHOLFiniteState s first with
  | mk result middle =>
    rw [evaluated] at run
    cases result with
    | none => exact ⟨middle,rfl,run⟩
    | some stopped => cases run

/-- Successful original extension tail pops the old record and delivers the
actual new parent. The stores may fail; normal completion itself rules that out. -/
theorem witness_extension_stores_normal_progress {F : Type}
    (s post : PanSemStateFiniteExact 64 F) (top heap prev : BitVec 64)
    (atTop : s.locals.lookup (ofString "top") = some (.val (.word top)))
    (atEx : s.locals.lookup (ofString "ex") = some (.val (.word heap)))
    (prevCell : s.memory top = .word prev)
    (before : top.toNat < heap.toNat) (heapBound : heap.toNat ≤ 33806089496)
    (run : evaluateHOLFiniteState s witnessExtensionStores = (none,post)) :
    post.locals.lookup (ofString "top") = some (.val (.word prev)) ∧
    post.locals.lookup (ofString "result") = some (.val (.word heap)) ∧
    post.locals.lookup (ofString "mode") = s.locals.lookup (ofString "mode") ∧
    post.memory top = s.memory top := by
  have separate : ∀ offset ∈ ([8,16] : List Nat), top ≠ heap + BitVec.ofNat 64 offset := by
    intro offset inside same
    have small : offset ≤ 16 := by simp at inside; omega
    have addNat : (heap + BitVec.ofNat 64 offset).toNat = heap.toNat + offset := by
      rw [BitVec.toNat_add,BitVec.toNat_ofNat]
      omega
    have eq := congrArg BitVec.toNat same
    rw [addNat] at eq
    omega
  rw [source_witness_extension_stores] at run
  obtain ⟨first,firstRun,firstLocals,tail⟩ := evaluate_store_sequence_normal s post _ _ _ run
  have firstFrame := evaluate_wordStore_memory_frame s
    (.op .add [.var .local (ofString "ex"),.const 8])
    (.load .one (.op .add [.var .local (ofString "top"),.const 48])) (heap+8) top
    (by simp [evalHOLExact,evalListHOLExact,atEx,wordOpHOL,wordOp,valueIsWord,valueWord])
    (fun parsed evaluated => eval_load_one_word s _ parsed evaluated) (separate 8 (by simp))
  rw [firstRun] at firstFrame
  obtain ⟨second,secondRun,secondLocals,tail⟩ := evaluate_store_sequence_normal first post _ _ _ tail
  have secondFrame := evaluate_wordStore_memory_frame first
    (.op .add [.var .local (ofString "ex"),.const 16])
    (.load .one (.op .add [.var .local (ofString "top"),.const 56])) (heap+16) top
    (by simp [evalHOLExact,evalListHOLExact,firstLocals,atEx,wordOpHOL,wordOp,valueIsWord,valueWord])
    (fun parsed evaluated => eval_load_one_word first _ parsed evaluated) (separate 16 (by simp))
  rw [secondRun] at secondFrame
  obtain ⟨popped,popRun,resultRun⟩ := witness_extension_sequence_normal_parts second post _ _ tail
  obtain ⟨loaded,popValue,poppedEq⟩ := evaluate_local_assign_normal_value second popped _ _ popRun
  obtain ⟨address,word,addressEval,accessible,cell,loadedEq⟩ := eval_load_one_read second _ loaded popValue
  have addressEq : address = top := by
    simpa [evalHOLExact,evalListHOLExact,secondLocals,firstLocals,atTop,
      wordOpHOL,wordOp,valueIsWord,valueWord] using addressEval.symm
  subst address
  have wordEq : word = prev := HolWordLab.word.inj
    (cell.symm.trans ((secondFrame.trans firstFrame).trans prevCell))
  subst word
  subst loaded
  obtain ⟨assigned,assignedValue,postEq⟩ := evaluate_local_assign_normal_value popped post _ _ resultRun
  have assignedEq : assigned = .val (.word heap) := by
    simpa [evalHOLExact,poppedEq,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,
      show ofString "top" ≠ ofString "ex" by decide,secondLocals,firstLocals,atEx] using assignedValue.symm
  subst assigned
  rw [postEq,poppedEq]
  refine ⟨?_,?_,?_,secondFrame.trans firstFrame⟩
  · simp [setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,
      show ofString "result" ≠ ofString "top" by decide]
  · simp [setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]
  · simp [setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,secondLocals,firstLocals,
      show ofString "result" ≠ ofString "mode" by decide,show ofString "top" ≠ ofString "mode" by decide]

#print axioms witness_extension_stores_normal_progress
end InitECandidate.Runtime
