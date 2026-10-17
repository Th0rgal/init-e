import InitECandidate.Runtime.TrieWalkRegistryInsertExtension
import InitECandidate.Runtime.AllocationAligned
import InitECandidate.Runtime.AllocationBodyBound
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- The original extension constructor establishes the full traversal registry
for its fresh parent, while preserving all old extension and branch records. -/
theorem evaluate_nodeNewExt_traversal_registry {F : Type} (state : PanSemStateFiniteExact 64 F)
    (live extensions branches : Set (BitVec 64)) (nibArgument sizeArgument childArgument : ExpHOL 64)
    (pointer nib size child : BitVec 64)
    (args : evalListHOLFinite state (h := fun address => Classical.propDecidable (state.memaddrs address))
      [nibArgument,sizeArgument,childArgument] = some [.val (.word nib),.val (.word size),.val (.word child)])
    (heap : state.globals.lookup (ofString "heap_ptr") = some (.val (.word pointer)))
    (code : state.code = originalRuntimeCode) (ticks : 2 ≤ state.clock)
    (positive : 0 < pointer.toNat) (budget : pointer.toNat + 56 ≤ 33806089496)
    (heapDomain : ∀ address : BitVec 64, address.toNat < 33806089496 → state.memaddrs address)
    (liveBefore : ∀ node ∈ live, node.toNat < pointer.toNat)
    (headers : ∀ node ∈ extensions, node.toNat + 56 ≤ pointer.toNat)
    (branchHeaders : ∀ node ∈ branches, node.toNat + 176 ≤ pointer.toNat)
    (childValid : child = 0 ∨ child ∈ live)
    (registry : TrieWalkRegistry live extensions branches state) :
    ∃ ready, evaluateHOLFiniteState state (.call (some (none,none)) (ofString "node_new_ext") [nibArgument,sizeArgument,childArgument]) = (none,ready) ∧
      ready.clock = state.clock - 2 ∧ ready.locals = state.locals ∧
      ready.globals.lookup (ofString "heap_ptr") = some (.val (.word (allocationEnd pointer 56))) ∧
      TrieWalkRegistry (insert pointer live) (insert pointer extensions) branches ready ∧
      (∀ node ∈ insert pointer live, node.toNat < (allocationEnd pointer 56).toNat) ∧
      (∀ node ∈ insert pointer extensions, node.toNat + 56 ≤ (allocationEnd pointer 56).toNat) ∧
      (∀ node ∈ branches, node.toNat + 176 ≤ (allocationEnd pointer 56).toNat) := by
  have naturalBudget : pointer.toNat + (56 : BitVec 64).toNat ≤ 33806089496 := budget
  have request := allocationGuard_of_sum_bound pointer 56 naturalBudget
  have finish := allocationEnd_within_heap pointer 56 (by omega) request
  have domain : ∀ offset ∈ ([0,8,16,24,32,40,48] : List Nat), state.memaddrs (pointer + BitVec.ofNat 64 offset) := by
    intro offset member
    have small : offset < 56 := by simp at member; omega
    have literal : (BitVec.ofNat 64 offset).toNat = offset := Nat.mod_eq_of_lt (by omega)
    have nextNat : (pointer + BitVec.ofNat 64 offset).toNat = pointer.toNat + offset := by
      rw [BitVec.toNat_add_of_lt (by rw [literal]; omega),literal]
    exact heapDomain _ (by rw [nextNat]; omega)
  have childBefore : child.toNat < pointer.toNat := by
    rcases childValid with zero | member
    · subst child; exact positive
    · exact liveBefore child member
  obtain ⟨ready,run,clock,locals,kind,_,childField,frontier,before,newOrder,declaration⟩ :=
    evaluate_nodeNewExt_call_and_declaration state nibArgument sizeArgument childArgument pointer nib size child args heap code ticks
      request finish budget domain childBefore
  have oldRegistry := registry.before_frame state ready live extensions branches pointer
    liveBefore headers branchHeaders before
  have newRegistry := TrieWalkRegistry.insert_extension ready live extensions branches pointer child
    oldRegistry kind newOrder childField childValid
  have covers := (allocationEnd_covers pointer 56 naturalBudget).1
  change pointer.toNat + 56 ≤ (allocationEnd pointer 56).toNat at covers
  refine ⟨ready,run,clock,locals,frontier,newRegistry,?_,?_,?_⟩
  · intro node member
    rcases Set.mem_insert_iff.mp member with same | old
    · subst node; omega
    · have below := liveBefore node old
      omega
  · intro node member
    rcases Set.mem_insert_iff.mp member with same | old
    · subst node; exact covers
    · have below := headers node old
      omega
  · intro node member
    have below := branchHeaders node member
    omega

#print axioms evaluate_nodeNewExt_traversal_registry
end InitECandidate.Runtime
