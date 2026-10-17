import InitECandidate.Runtime.ExtensionChildrenIn
import InitECandidate.Runtime.AllocationAligned
import InitECandidate.Runtime.AllocationBodyBound
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- The actual extension constructor extends live-node and extension registries.
Natural byte bounds imply both allocation guards and all store domains; child
membership supplies the strict pre-existing-child order automatically. -/
theorem evaluate_nodeNewExt_live_registry {F : Type} (state : PanSemStateFiniteExact 64 F)
    (live extensions : Set (BitVec 64)) (nibArgument sizeArgument childArgument : ExpHOL 64)
    (pointer nib size child : BitVec 64)
    (args : evalListHOLFinite state (h := fun address => Classical.propDecidable (state.memaddrs address))
      [nibArgument,sizeArgument,childArgument] = some [.val (.word nib),.val (.word size),.val (.word child)])
    (heap : state.globals.lookup (ofString "heap_ptr") = some (.val (.word pointer)))
    (code : state.code = originalRuntimeCode) (ticks : 2 ≤ state.clock)
    (positive : 0 < pointer.toNat) (budget : pointer.toNat + 56 ≤ 33806089496)
    (heapDomain : ∀ address : BitVec 64, address.toNat < 33806089496 → state.memaddrs address)
    (included : extensions ⊆ live)
    (liveBefore : ∀ node ∈ live, node.toNat < pointer.toNat)
    (headers : ∀ node ∈ extensions, node.toNat + 56 ≤ pointer.toNat)
    (childValid : child = 0 ∨ child ∈ live)
    (order : ExtensionOrderFamily extensions state)
    (children : ExtensionChildrenIn live extensions state) :
    ∃ ready, evaluateHOLFiniteState state (.call (some (none,none)) (ofString "node_new_ext") [nibArgument,sizeArgument,childArgument]) = (none,ready) ∧
      ready.clock = state.clock - 2 ∧ ready.locals = state.locals ∧
      ready.globals.lookup (ofString "heap_ptr") = some (.val (.word (allocationEnd pointer 56))) ∧
      pointer ∉ live ∧ insert pointer extensions ⊆ insert pointer live ∧
      ExtensionOrderFamily (insert pointer extensions) ready ∧
      ExtensionChildrenIn (insert pointer live) (insert pointer extensions) ready ∧
      (∀ node ∈ insert pointer live, node.toNat < (allocationEnd pointer 56).toNat) ∧
      (∀ node ∈ insert pointer extensions, node.toNat + 56 ≤ (allocationEnd pointer 56).toNat) ∧
      (∀ name continuation, evaluateHOLFiniteState state (.decCall name .one (ofString "node_new_ext") [nibArgument,sizeArgument,childArgument] continuation) =
        (let output := evaluateHOLFiniteState (setVarHOLFinite name (.val (.word pointer)) ready) continuation;
          (output.1,{output.2 with locals := HolFiniteMapExact.resVarEq output.2.locals (name,state.locals.lookup name)}))) := by
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
  obtain ⟨ready,run,clock,locals,_,_,childField,frontier,before,newOrder,declaration⟩ :=
    evaluate_nodeNewExt_call_and_declaration state nibArgument sizeArgument childArgument pointer nib size child args heap code ticks
      request finish budget domain childBefore
  have oldOrder := extensionOrderFamily_before_frame state ready extensions pointer order headers before
  have oldChildren := extensionChildrenIn_before_frame state ready live extensions pointer children headers before
  have covers := (allocationEnd_covers pointer 56 naturalBudget).1
  change pointer.toNat + 56 ≤ (allocationEnd pointer 56).toNat at covers
  refine ⟨ready,run,clock,locals,frontier,?_,?_,?_,?_,?_,?_,declaration⟩
  · intro member
    have below := liveBefore pointer member
    omega
  · intro node member
    rcases Set.mem_insert_iff.mp member with same | old
    · subst node; exact Set.mem_insert _ _
    · exact Set.mem_insert_of_mem _ (included old)
  · intro node member
    rcases Set.mem_insert_iff.mp member with same | old
    · subst node; exact newOrder
    · exact oldOrder node old
  · intro node member next loaded
    rcases Set.mem_insert_iff.mp member with same | old
    · subst node
      have equal : child = next := HolWordLab.word.inj (childField.symm.trans loaded)
      subst next
      rcases childValid with zero | oldChild
      · exact Or.inl zero
      · exact Or.inr (Set.mem_insert_of_mem _ oldChild)
    · rcases oldChildren node old next loaded with zero | oldChild
      · exact Or.inl zero
      · exact Or.inr (Set.mem_insert_of_mem _ oldChild)
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

#print axioms evaluate_nodeNewExt_live_registry
end InitECandidate.Runtime
