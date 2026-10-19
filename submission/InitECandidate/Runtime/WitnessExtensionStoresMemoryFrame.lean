import InitECandidate.Runtime.WitnessExtensionStoresProgress
import InitECandidate.Runtime.BoundWordStoreChainFrame
import InitECandidate.Runtime.GlobalsFrameComposition
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
/-- Every actual extension tail outcome frames all words below the new parent. -/
theorem witness_extension_stores_memory_below_heap {F : Type}
    (s : PanSemStateFiniteExact 64 F) (heap watched : BitVec 64)
    (atEx : s.locals.lookup (ofString "ex")=some (.val (.word heap)))
    (heapBound : heap.toNat≤33806089496) (before : watched.toNat<heap.toNat) :
    (evaluateHOLFiniteState s witnessExtensionStores).2.memory watched=s.memory watched := by
  have separate (offset : Nat) (small : offset≤16) : watched≠heap+BitVec.ofNat 64 offset := by
    intro same
    have addNat : (heap+BitVec.ofNat 64 offset).toNat=heap.toNat+offset := by
      rw [BitVec.toNat_add,BitVec.toNat_ofNat];omega
    have equal := congrArg BitVec.toNat same
    rw [addNat] at equal
    omega
  have supported : BoundWordStoreChainFrame (F := F) s.locals watched witnessExtensionStores := by
    rw [source_witness_extension_stores]
    apply BoundWordStoreChainFrame.store
    · intro state locals
      refine ⟨heap+8,?_,separate 8 (by decide)⟩
      simp [evalHOLExact,evalListHOLExact,locals,atEx,wordOpHOL,wordOp,valueIsWord,valueWord]
    · intro state locals parsed evaluated
      exact eval_load_one_word state _ parsed evaluated
    apply BoundWordStoreChainFrame.store
    · intro state locals
      refine ⟨heap+16,?_,separate 16 (by decide)⟩
      simp [evalHOLExact,evalListHOLExact,locals,atEx,wordOpHOL,wordOp,valueIsWord,valueWord]
    · intro state locals parsed evaluated
      exact eval_load_one_word state _ parsed evaluated
    exact .tail _ rfl
  exact evaluate_boundWordStoreChain_frame supported s rfl

theorem witness_extension_stores_globals_frame : OriginalGlobalsFrame witnessExtensionStores := by
  apply originalGlobalsFrame_leaf
  intro watched
  rw [source_witness_extension_stores]
  rfl
#print axioms witness_extension_stores_memory_below_heap
#print axioms witness_extension_stores_globals_frame
end InitECandidate.Runtime
