import InitECandidate.Runtime.NodeNewLeafLayout
import InitECandidate.Runtime.TrieNibbleAllocationFrame
import InitECandidate.Runtime.PanEvaluationMetadata
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- A real leaf constructor preserves its previously allocated nibble path
while extending both the traversal registry and allocated-node layout. -/
theorem evaluate_nodeNewLeaf_layout_path {F : Type} (state : PanSemStateFiniteExact 64 F)
    (live extensions branches : Set (BitVec 64)) (size : BitVec 64 → Nat) (nibArgument sizeArgument valueArgument lengthArgument : ExpHOL 64)
    (pointer nib nlen vptr vlen : BitVec 64)
    (args : evalListHOLFinite state (h := fun address => Classical.propDecidable (state.memaddrs address))
      [nibArgument,sizeArgument,valueArgument,lengthArgument] = some [.val (.word nib),.val (.word nlen),.val (.word vptr),.val (.word vlen)])
    (heap : state.globals.lookup (ofString "heap_ptr") = some (.val (.word pointer)))
    (code : state.code = originalRuntimeCode) (ticks : 2 ≤ state.clock)
    (budget : pointer.toNat + 64 ≤ 33806089496)
    (heapDomain : ∀ address : BitVec 64, address.toNat < 33806089496 → state.memaddrs address)
    (registry : TrieWalkRegistry live extensions branches state)
    (layout : TrieNodeLayout live extensions branches size)
    (path : TrieNibbleRange state nib nlen)
    (pathBefore : nib.toNat + nlen.toNat ≤ pointer.toNat)
    (frontier : ∀ node ∈ live, node.toNat + size node ≤ pointer.toNat) :
    ∃ ready, evaluateHOLFiniteState state (.call (some (none,none)) (ofString "node_new_leaf") [nibArgument,sizeArgument,valueArgument,lengthArgument]) = (none,ready) ∧
      ready.clock = state.clock - 2 ∧ ready.locals = state.locals ∧
      ready.globals.lookup (ofString "heap_ptr") = some (.val (.word (allocationEnd pointer 64))) ∧
      TrieNibbleRange ready nib nlen ∧
      TrieWalkRegistry (insert pointer live) extensions branches ready ∧
      TrieNodeLayout (insert pointer live) extensions branches (trieRecordSizeInsert size pointer 64) ∧
      (∀ node ∈ insert pointer live,
        node.toNat + trieRecordSizeInsert size pointer 64 node ≤ (allocationEnd pointer 64).toNat) := by
  obtain ⟨ready,run,clock,locals,heapNext,registered,allocated,nextFrontier⟩ :=
    evaluate_nodeNewLeaf_layout state live extensions branches size nibArgument sizeArgument valueArgument lengthArgument
      pointer nib nlen vptr vlen args heap code ticks budget heapDomain registry layout frontier
  have request := allocationGuard_of_sum_bound pointer 64 (show pointer.toNat + (64 : BitVec 64).toNat ≤ 33806089496 from budget)
  have finish := allocationEnd_within_heap pointer 64 (by omega) request
  have domain : ∀ offset ∈ ([0,8,16,24,32,40,48,56] : List Nat), state.memaddrs (pointer + BitVec.ofNat 64 offset) := by
    intro offset member
    have small : offset < 64 := by simp at member; omega
    have natural : (pointer + BitVec.ofNat 64 offset).toNat = pointer.toNat + offset := by
      rw [BitVec.toNat_add,BitVec.toNat_ofNat]
      omega
    exact heapDomain _ (by rw [natural]; omega)
  obtain ⟨other,otherRun,_,_,_,_,before,_⟩ := evaluate_nodeNewLeaf_call_and_declaration state
    nibArgument sizeArgument valueArgument lengthArgument pointer nib nlen vptr vlen args heap code ticks
    request finish budget domain
  have equal : other = ready := (Prod.mk.inj (otherRun.symm.trans run)).2
  subst other
  have metadata := evaluateHOLFiniteState_metadata state
    (.call (some (none,none)) (ofString "node_new_leaf") [nibArgument,sizeArgument,valueArgument,lengthArgument])
  rw [run] at metadata
  dsimp only at metadata
  have preserved : TrieNibbleRange ready nib nlen := path.before_allocation pointer pathBefore before metadata.2.1 metadata.2.2.1
  exact ⟨ready,run,clock,locals,heapNext,preserved,registered,allocated,nextFrontier⟩

#print axioms evaluate_nodeNewLeaf_layout_path
end InitECandidate.Runtime
