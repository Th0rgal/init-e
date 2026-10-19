import InitECandidate.Runtime.WitnessBranchFinishSource
import InitECandidate.Runtime.BoundWordStoreChainFrame
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

def witnessBranchValueUpdate : ProgHOL 64 :=
  match witnessBranchFinishAt 3 with | .seq update _ => update | _ => .skip

def witnessBranchValueStores : ProgHOL 64 :=
  match witnessBranchValueUpdate with | .ite _ stores _ => stores | _ => .skip

theorem source_witness_branch_value_sequence : witnessBranchFinishAt 3 =
  .seq witnessBranchValueUpdate (witnessBranchFinishAt 4) := by
  simp only [witnessBranchValueUpdate,source_witness_branch_finish_value]

theorem source_witness_branch_value_update : witnessBranchValueUpdate =
  .ite (.cmp .equal (.rfield 0 (.var .local (ofString "bv"))) (.const 0)) witnessBranchValueStores .skip := by
  simp only [witnessBranchValueUpdate,witnessBranchValueStores,source_witness_branch_finish_value]

theorem source_witness_branch_value_stores : witnessBranchValueStores =
  .seq (.store (.op .add [.var .local (ofString "br"),.const 160]) (.rfield 1 (.var .local (ofString "bv"))))
    (.seq (.store (.op .add [.var .local (ofString "br"),.const 168]) (.rfield 2 (.var .local (ofString "bv"))))
      (.ite (.cmp .notEqual (.rfield 2 (.var .local (ofString "bv"))) (.const 0))
        (.assign .local (ofString "occ") (.op .add [.var .local (ofString "occ"),.const 1])) .skip)) := by
  simp only [witnessBranchValueStores,witnessBranchValueUpdate,source_witness_branch_finish_value]

/-- Actual final-value cache writes cannot overwrite the older scratch record
or any word below the branch node, including failed stores and bad guards. -/
theorem witness_branch_value_update_word_frame {F : Type} (s : PanSemStateFiniteExact 64 F)
    (heap kind pointer length consumed watched : BitVec 64)
    (atBr : s.locals.lookup (ofString "br") = some (.val (.word heap)))
    (atValue : s.locals.lookup (ofString "bv") = some
      (.rStruct [.val (.word kind),.val (.word pointer),.val (.word length),.val (.word consumed)]))
    (heapBound : heap.toNat ≤ 33806089496) (before : watched.toNat < heap.toNat) :
    (evaluateHOLFiniteState s witnessBranchValueUpdate).2.memory watched = s.memory watched := by
  have separate (offset : Nat) (small : offset ≤ 168) : watched ≠ heap+BitVec.ofNat 64 offset := by
    intro same
    have addNat : (heap+BitVec.ofNat 64 offset).toNat = heap.toNat+offset := by
      rw [BitVec.toNat_add,BitVec.toNat_ofNat]; omega
    have equal := congrArg BitVec.toNat same
    rw [addNat] at equal
    omega
  have supported : BoundWordStoreChainFrame (F := F) s.locals watched witnessBranchValueStores := by
    rw [source_witness_branch_value_stores]
    apply BoundWordStoreChainFrame.store
    · intro state locals
      refine ⟨heap+160,?_,separate 160 (by decide)⟩
      simp [evalHOLExact,evalListHOLExact,locals,atBr,wordOpHOL,wordOp,valueIsWord,valueWord]
    · intro state locals parsed evaluated
      exact ⟨pointer,by simpa [evalHOLExact,locals,atValue] using evaluated.symm⟩
    apply BoundWordStoreChainFrame.store
    · intro state locals
      refine ⟨heap+168,?_,separate 168 (by decide)⟩
      simp [evalHOLExact,evalListHOLExact,locals,atBr,wordOpHOL,wordOp,valueIsWord,valueWord]
    · intro state locals parsed evaluated
      exact ⟨length,by simpa [evalHOLExact,locals,atValue] using evaluated.symm⟩
    exact .tail _ rfl
  have stores := evaluate_boundWordStoreChain_frame supported s rfl
  rw [source_witness_branch_value_update,evaluateHOLFiniteState_ite]
  split
  · split
    · rw [evaluateHOLFiniteState_skip]
    · exact stores
  · rfl

#print axioms source_witness_branch_value_sequence
#print axioms source_witness_branch_value_update
#print axioms source_witness_branch_value_stores
#print axioms witness_branch_value_update_word_frame
end InitECandidate.Runtime
