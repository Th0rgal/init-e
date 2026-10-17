import InitECandidate.Runtime.NodeNewExtTraversalRegistry
import InitECandidate.Runtime.TrieNodeLayoutAllocation
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- Actual ext construction extends both the traversal registry and the
allocated-record layout, carrying the updated frontier to later constructors. -/
theorem evaluate_nodeNewExt_layout {F : Type} (state : PanSemStateFiniteExact 64 F)
    (live extensions branches : Set (BitVec 64)) (size : BitVec 64 → Nat) (nibArgument sizeArgument childArgument : ExpHOL 64)
    (pointer nib nlen child : BitVec 64)
    (args : evalListHOLFinite state (h := fun address => Classical.propDecidable (state.memaddrs address))
      [nibArgument,sizeArgument,childArgument] = some [.val (.word nib),.val (.word nlen),.val (.word child)])
    (heap : state.globals.lookup (ofString "heap_ptr") = some (.val (.word pointer)))
    (code : state.code = originalRuntimeCode) (ticks : 2 ≤ state.clock)
    (positive : 0 < pointer.toNat) (budget : pointer.toNat + 56 ≤ 33806089496)
    (heapDomain : ∀ address : BitVec 64, address.toNat < 33806089496 → state.memaddrs address)
    (childValid : child = 0 ∨ child ∈ live)
    (registry : TrieWalkRegistry live extensions branches state)
    (layout : TrieNodeLayout live extensions branches size)
    (frontier : ∀ node ∈ live, node.toNat + size node ≤ pointer.toNat) :
    ∃ ready, evaluateHOLFiniteState state (.call (some (none,none)) (ofString "node_new_ext") [nibArgument,sizeArgument,childArgument]) = (none,ready) ∧
      ready.clock = state.clock - 2 ∧ ready.locals = state.locals ∧
      ready.globals.lookup (ofString "heap_ptr") = some (.val (.word (allocationEnd pointer 56))) ∧
      TrieWalkRegistry (insert pointer live) (insert pointer extensions) branches ready ∧
      TrieNodeLayout (insert pointer live) (insert pointer extensions) branches (trieRecordSizeInsert size pointer 56) ∧
      (∀ node ∈ insert pointer live,
        node.toNat + trieRecordSizeInsert size pointer 56 node ≤ (allocationEnd pointer 56).toNat) := by
  have liveBefore : ∀ node ∈ live, node.toNat < pointer.toNat := by
    intro node member
    have nonempty := layout.positive node member
    have endBound := frontier node member
    omega
  have headers : ∀ node ∈ extensions, node.toNat + 56 ≤ pointer.toNat := by
    intro node member
    have record := layout.extensionSize node member
    have endBound := frontier node (layout.extensionLive member)
    omega
  have branchHeaders : ∀ node ∈ branches, node.toNat + 176 ≤ pointer.toNat := by
    intro node member
    have record := layout.branchSize node member
    have endBound := frontier node (layout.branchLive member)
    omega
  obtain ⟨ready,run,clock,locals,heapNext,registered,_⟩ := evaluate_nodeNewExt_traversal_registry
    state live extensions branches nibArgument sizeArgument childArgument pointer nib nlen child args heap code ticks positive budget heapDomain liveBefore headers branchHeaders childValid registry
  have allocated := layout.allocate pointer 56 (by decide) (by omega) frontier
  have fresh : pointer ∉ live := by intro member; have before := liveBefore pointer member; omega
  have notBranch : pointer ∉ branches := fun member => fresh (layout.branchLive member)
  have classified := allocated.register_extension pointer (Set.mem_insert _ _) (by simp [trieRecordSizeInsert]) notBranch
  have covers := (allocationEnd_covers pointer 56 (by exact budget)).1
  change pointer.toNat + 56 ≤ (allocationEnd pointer 56).toNat at covers
  exact ⟨ready,run,clock,locals,heapNext,registered,classified,
    layout.allocate_frontier pointer 56 (allocationEnd pointer 56).toNat frontier covers⟩

#print axioms evaluate_nodeNewExt_layout
end InitECandidate.Runtime
