import InitECandidate.Runtime.WitnessBranchFinishGuardProgress
import InitECandidate.Runtime.WitnessBranchValueFrame
import InitECandidate.Runtime.AvoidsLocalFrame
import InitECandidate.Runtime.BoundWordStoreChainFrame
import InitECandidate.Runtime.GlobalsFrameComposition
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
/-- Every actual extension tail outcome frames all words below the new parent. -/
theorem witness_branch_finish_stores_memory_below_heap {F : Type}
    (s : PanSemStateFiniteExact 64 F) (heap watched : BitVec 64)
    (atBr : s.locals.lookup (ofString "br")=some (.val (.word heap)))
    (heapBound : heap.toNat≤33806089496) (before : watched.toNat<heap.toNat) :
    (evaluateHOLFiniteState s (witnessBranchFinishAt 5)).2.memory watched=s.memory watched := by
  have separate (offset : Nat) (small : offset≤16) : watched≠heap+BitVec.ofNat 64 offset := by
    intro same
    have addNat : (heap+BitVec.ofNat 64 offset).toNat=heap.toNat+offset := by
      rw [BitVec.toNat_add,BitVec.toNat_ofNat];omega
    have equal := congrArg BitVec.toNat same
    rw [addNat] at equal
    omega
  have supported : BoundWordStoreChainFrame (F := F) s.locals watched (witnessBranchFinishAt 5) := by
    rw [source_witness_branch_finish_stores]
    apply BoundWordStoreChainFrame.store
    · intro state locals
      refine ⟨heap+8,?_,separate 8 (by decide)⟩
      simp [evalHOLExact,evalListHOLExact,locals,atBr,wordOpHOL,wordOp,valueIsWord,valueWord]
    · intro state locals parsed evaluated
      exact eval_load_one_word state _ parsed evaluated
    apply BoundWordStoreChainFrame.store
    · intro state locals
      refine ⟨heap+16,?_,separate 16 (by decide)⟩
      simp [evalHOLExact,evalListHOLExact,locals,atBr,wordOpHOL,wordOp,valueIsWord,valueWord]
    · intro state locals parsed evaluated
      exact eval_load_one_word state _ parsed evaluated
    exact .tail _ rfl
  exact evaluate_boundWordStoreChain_frame supported s rfl

theorem witness_branch_finish_stores_globals_frame : OriginalGlobalsFrame (witnessBranchFinishAt 5) := by
  apply originalGlobalsFrame_leaf
  intro watched
  rw [source_witness_branch_finish_stores]
  rfl
theorem witness_branch_finish_guard_normal_memory_frame {F : Type}
    (s post : PanSemStateFiniteExact 64 F) (heap : BitVec 64)
    (atBr : s.locals.lookup (ofString "br")=some (.val (.word heap)))
    (heapBound : heap.toNat≤33806089496) (code : s.code=originalRuntimeCode)
    (run : evaluateHOLFiniteState s (witnessBranchFinishAt 4)=(none,post)) :
    post.globals=s.globals ∧ ∀ watched : BitVec 64, watched.toNat<heap.toNat → post.memory watched=s.memory watched := by
  rw [source_witness_branch_finish_guard] at run
  obtain ⟨next,guardRun,tailRun⟩ := witness_extension_sequence_normal_parts s post _ _ run
  have same := mpt_fail_guard_normal_state s next _ 9 code guardRun
  subst next
  have globals := witness_branch_finish_stores_globals_frame s code
  rw [tailRun] at globals
  refine ⟨globals,?_⟩
  intro watched before
  have memory := witness_branch_finish_stores_memory_below_heap s heap watched atBr heapBound before
  rw [tailRun] at memory
  exact memory

theorem witness_branch_finish_value_normal_memory_frame {F : Type}
    (s post : PanSemStateFiniteExact 64 F) (heap kind pointer length consumed : BitVec 64)
    (atBr : s.locals.lookup (ofString "br")=some (.val (.word heap)))
    (atValue : s.locals.lookup (ofString "bv")=some
      (.rStruct [.val (.word kind),.val (.word pointer),.val (.word length),.val (.word consumed)]))
    (heapBound : heap.toNat≤33806089496) (code : s.code=originalRuntimeCode)
    (run : evaluateHOLFiniteState s (witnessBranchFinishAt 3)=(none,post)) :
    post.globals=s.globals ∧ ∀ watched : BitVec 64, watched.toNat<heap.toNat → post.memory watched=s.memory watched := by
  rw [source_witness_branch_value_sequence] at run
  obtain ⟨next,normal,tailRun⟩ := witness_extension_sequence_normal_parts s post _ _ run
  have brFrame := evaluate_avoidsLocal_flowing (ofString "br") witnessBranchValueUpdate
    (by rw [source_witness_branch_value_update,source_witness_branch_value_stores];decide) s
    (by rw [normal];exact Or.inl rfl)
  have globalFrame : OriginalGlobalsFrame witnessBranchValueUpdate := by
    apply originalGlobalsFrame_leaf
    intro watched
    rw [source_witness_branch_value_update,source_witness_branch_value_stores]
    rfl
  have globals := globalFrame s code
  have metadata := evaluateHOLFiniteState_metadata s witnessBranchValueUpdate
  rw [normal] at brFrame globals metadata
  obtain ⟨tailGlobals,tailMemory⟩ := witness_branch_finish_guard_normal_memory_frame next post heap
    (brFrame.trans atBr) heapBound (metadata.1.trans code) tailRun
  refine ⟨tailGlobals.trans globals,?_⟩
  intro watched before
  have memory := witness_branch_value_update_word_frame s heap kind pointer length consumed watched atBr atValue heapBound before
  rw [normal] at memory
  exact (tailMemory watched before).trans memory

theorem witness_branch_finish_suffix_normal_memory_frame {F : Type}
    (s post : PanSemStateFiniteExact 64 F) (heap kind pointer length consumed : BitVec 64)
    (atBr : s.locals.lookup (ofString "br")=some (.val (.word heap)))
    (atValue : s.locals.lookup (ofString "bv")=some
      (.rStruct [.val (.word kind),.val (.word pointer),.val (.word length),.val (.word consumed)]))
    (heapBound : heap.toNat≤33806089496) (code : s.code=originalRuntimeCode)
    (run : evaluateHOLFiniteState s (witnessBranchFinishAt 2)=(none,post)) :
    post.globals=s.globals ∧ ∀ watched : BitVec 64, watched.toNat<heap.toNat → post.memory watched=s.memory watched := by
  rw [source_witness_branch_finish_occupancy] at run
  obtain ⟨value,output,_,bodyRun,postEq⟩ := evaluate_dec_normal_scope s post _ _ _ _ run
  let entered := setVarHOLFinite (ofString "occ") value s
  have other (name : MlS) (different : name≠ofString "occ") : entered.locals.lookup name=s.locals.lookup name := by
    simp [entered,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,Ne.symm different]
  have facts := witness_branch_finish_value_normal_memory_frame entered output heap kind pointer length consumed
    ((other _ (by decide)).trans atBr) ((other _ (by decide)).trans atValue) heapBound code bodyRun
  rw [postEq]
  exact facts
#print axioms witness_branch_finish_guard_normal_memory_frame
#print axioms witness_branch_finish_value_normal_memory_frame
#print axioms witness_branch_finish_suffix_normal_memory_frame
#print axioms witness_branch_finish_stores_memory_below_heap
#print axioms witness_branch_finish_stores_globals_frame
end InitECandidate.Runtime
