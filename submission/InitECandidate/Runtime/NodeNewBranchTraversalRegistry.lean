import InitECandidate.Runtime.TrieWalkRegistryInsertBranch
import InitECandidate.Runtime.NodeNewBranchCall
import InitECandidate.Runtime.AllocationAligned
import InitECandidate.Runtime.AllocationBodyBound
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- The original branch constructor establishes the full traversal registry
for its fresh record, preserving all old extension and branch records. -/
theorem evaluate_nodeNewBranch_traversal_registry {F : Type} (state : PanSemStateFiniteExact 64 F)
    (live extensions branches : Set (BitVec 64)) (pointer : BitVec 64)
    (heap : state.globals.lookup (ofString "heap_ptr") = some (.val (.word pointer)))
    (code : state.code = originalRuntimeCode) (ticks : 179 ≤ state.clock)
    (aligned : pointer.toNat % 8 = 0) (budget : pointer.toNat + 176 ≤ 33806089496)
    (heapDomain : ∀ address : BitVec 64, address.toNat < 33806089496 → state.memaddrs address)
    (liveBefore : ∀ node ∈ live, node.toNat < pointer.toNat)
    (headers : ∀ node ∈ extensions, node.toNat + 56 ≤ pointer.toNat)
    (branchHeaders : ∀ node ∈ branches, node.toNat + 176 ≤ pointer.toNat)
    (registry : TrieWalkRegistry live extensions branches state) :
    ∃ ready, evaluateHOLFiniteState state (.call (some (none,none)) (ofString "node_new_branch") []) = (none,ready) ∧
      state.clock ≤ ready.clock + 179 ∧ ready.clock ≤ state.clock ∧ ready.locals = state.locals ∧
      ready.globals.lookup (ofString "heap_ptr") = some (.val (.word (allocationEnd pointer 176))) ∧
      TrieWalkRegistry (insert pointer live) extensions (insert pointer branches) ready ∧
      (∀ node ∈ insert pointer live, node.toNat < (allocationEnd pointer 176).toNat) ∧
      (∀ node ∈ extensions, node.toNat + 56 ≤ (allocationEnd pointer 176).toNat) ∧
      (∀ node ∈ insert pointer branches, node.toNat + 176 ≤ (allocationEnd pointer 176).toNat) := by
  have naturalBudget : pointer.toNat + (176 : BitVec 64).toNat ≤ 33806089496 := budget
  have request := allocationGuard_of_sum_bound pointer 176 naturalBudget
  have finish := allocationEnd_within_heap pointer 176 (by omega) request
  have wordDomain : ∀ offset : Nat, offset < 176 → state.memaddrs (pointer + BitVec.ofNat 64 offset) := by
    intro offset small
    have natural : (pointer + BitVec.ofNat 64 offset).toNat = pointer.toNat + offset := by
      rw [BitVec.toNat_add,BitVec.toNat_ofNat]
      omega
    exact heapDomain _ (by rw [natural]; omega)
  have byteDomain : ∀ offset : Nat, offset < 176 → state.memaddrs (panByteAlignHOL (pointer + BitVec.ofNat 64 offset)) := by
    intro offset small
    have natural : (pointer + BitVec.ofNat 64 offset).toNat = pointer.toNat + offset := by
      rw [BitVec.toNat_add,BitVec.toNat_ofNat]
      omega
    apply heapDomain
    rw [panByteAlign_toNat64,natural]
    have rounded := Nat.div_mul_le_self (pointer.toNat + offset) 8
    omega
  obtain ⟨ready,run,cost,remaining,locals,kind,children,frontier,before,_⟩ :=
    evaluate_nodeNewBranch_call_and_declaration state pointer heap code ticks request finish budget aligned wordDomain byteDomain
  have oldRegistry := registry.before_frame state ready live extensions branches pointer
    liveBefore headers branchHeaders before
  have newRegistry := TrieWalkRegistry.insert_branch ready live extensions branches pointer oldRegistry kind children
  have covers := (allocationEnd_covers pointer 176 naturalBudget).1
  change pointer.toNat + 176 ≤ (allocationEnd pointer 176).toNat at covers
  refine ⟨ready,run,cost,remaining,locals,frontier,newRegistry,?_,?_,?_⟩
  · intro node member
    rcases Set.mem_insert_iff.mp member with same | old
    · subst node; omega
    · have below := liveBefore node old
      omega
  · intro node member
    have below := headers node member
    omega
  · intro node member
    rcases Set.mem_insert_iff.mp member with same | old
    · subst node; exact covers
    · have below := branchHeaders node old
      omega

#print axioms evaluate_nodeNewBranch_traversal_registry
end InitECandidate.Runtime
