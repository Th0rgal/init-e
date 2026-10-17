import InitECandidate.Runtime.TrieWalkRegistryInsertTerminal
import InitECandidate.Runtime.TrieWalkRegistryAllocationFrame
import InitECandidate.Runtime.NodeNewLeafCall
import InitECandidate.Runtime.AllocationAligned
import InitECandidate.Runtime.AllocationBodyBound
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- The original leaf constructor adds a terminal live node and preserves
all extension and branch records and their allocation bounds. -/
theorem evaluate_nodeNewLeaf_traversal_registry {F : Type} (state : PanSemStateFiniteExact 64 F)
    (live extensions branches : Set (BitVec 64)) (nibArgument sizeArgument valueArgument lengthArgument : ExpHOL 64)
    (pointer nib nlen vptr vlen : BitVec 64)
    (args : evalListHOLFinite state (h := fun address => Classical.propDecidable (state.memaddrs address))
      [nibArgument,sizeArgument,valueArgument,lengthArgument] = some [.val (.word nib),.val (.word nlen),.val (.word vptr),.val (.word vlen)])
    (heap : state.globals.lookup (ofString "heap_ptr") = some (.val (.word pointer)))
    (code : state.code = originalRuntimeCode) (ticks : 2 ≤ state.clock)
    (budget : pointer.toNat + 64 ≤ 33806089496)
    (heapDomain : ∀ address : BitVec 64, address.toNat < 33806089496 → state.memaddrs address)
    (liveBefore : ∀ node ∈ live, node.toNat < pointer.toNat)
    (headers : ∀ node ∈ extensions, node.toNat + 56 ≤ pointer.toNat)
    (branchHeaders : ∀ node ∈ branches, node.toNat + 176 ≤ pointer.toNat)
    (registry : TrieWalkRegistry live extensions branches state) :
    ∃ ready, evaluateHOLFiniteState state (.call (some (none,none)) (ofString "node_new_leaf") [nibArgument,sizeArgument,valueArgument,lengthArgument]) = (none,ready) ∧
      ready.clock = state.clock - 2 ∧ ready.locals = state.locals ∧
      ready.globals.lookup (ofString "heap_ptr") = some (.val (.word (allocationEnd pointer 64))) ∧
      TrieWalkRegistry (insert pointer live) extensions branches ready ∧
      (∀ node ∈ insert pointer live, node.toNat < (allocationEnd pointer 64).toNat) ∧
      (∀ node ∈ extensions, node.toNat + 56 ≤ (allocationEnd pointer 64).toNat) ∧
      (∀ node ∈ branches, node.toNat + 176 ≤ (allocationEnd pointer 64).toNat) := by
  have naturalBudget : pointer.toNat + (64 : BitVec 64).toNat ≤ 33806089496 := budget
  have request := allocationGuard_of_sum_bound pointer 64 naturalBudget
  have finish := allocationEnd_within_heap pointer 64 (by omega) request
  have domain : ∀ offset ∈ ([0,8,16,24,32,40,48,56] : List Nat), state.memaddrs (pointer + BitVec.ofNat 64 offset) := by
    intro offset member
    have small : offset < 64 := by simp at member; omega
    have natural : (pointer + BitVec.ofNat 64 offset).toNat = pointer.toNat + offset := by
      rw [BitVec.toNat_add,BitVec.toNat_ofNat]
      omega
    exact heapDomain _ (by rw [natural]; omega)
  obtain ⟨ready,run,clock,locals,kind,frontier,before,_⟩ :=
    evaluate_nodeNewLeaf_call_and_declaration state nibArgument sizeArgument valueArgument lengthArgument pointer nib nlen vptr vlen args heap code ticks request finish budget domain
  have oldRegistry := registry.before_frame state ready live extensions branches pointer
    liveBefore headers branchHeaders before
  have newRegistry := TrieWalkRegistry.insert_terminal ready live extensions branches pointer 1 oldRegistry kind (Or.inr rfl)
  have covers := (allocationEnd_covers pointer 64 naturalBudget).1
  change pointer.toNat + 64 ≤ (allocationEnd pointer 64).toNat at covers
  refine ⟨ready,run,clock,locals,frontier,newRegistry,?_,?_,?_⟩
  · intro node member
    rcases Set.mem_insert_iff.mp member with same | old
    · subst node; omega
    · have below := liveBefore node old
      omega
  · intro node member
    have below := headers node member
    omega
  · intro node member
    have below := branchHeaders node member
    omega

#print axioms evaluate_nodeNewLeaf_traversal_registry
end InitECandidate.Runtime
