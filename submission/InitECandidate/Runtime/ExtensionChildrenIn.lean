import InitECandidate.Runtime.NodeNewExtOrderRegistry
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact

/-- Every registered extension child is null or a registered live node. -/
def ExtensionChildrenIn {F : Type} (live extensions : Set (BitVec 64)) (state : PanSemStateFiniteExact 64 F) : Prop :=
  ∀ node ∈ extensions, ∀ child : BitVec 64, state.memory (node + 48) = .word child → child = 0 ∨ child ∈ live

theorem extensionChildrenIn_empty {F : Type} (live : Set (BitVec 64)) (state : PanSemStateFiniteExact 64 F) :
    ExtensionChildrenIn live ∅ state := by intro node member; cases member

theorem ExtensionChildrenIn.mono {F : Type} {state : PanSemStateFiniteExact 64 F}
    {live larger extensions : Set (BitVec 64)} (included : live ⊆ larger)
    (valid : ExtensionChildrenIn live extensions state) : ExtensionChildrenIn larger extensions state := by
  intro node member child loaded
  rcases valid node member child loaded with zero | old
  · exact Or.inl zero
  · exact Or.inr (included old)

/-- Writes after the allocation frontier preserve all earlier extension edges. -/
theorem extensionChildrenIn_before_frame {F : Type} (state post : PanSemStateFiniteExact 64 F)
    (live extensions : Set (BitVec 64)) (pointer : BitVec 64)
    (children : ExtensionChildrenIn live extensions state)
    (headers : ∀ node ∈ extensions, node.toNat + 56 ≤ pointer.toNat)
    (frame : ∀ address : BitVec 64, address.toNat < pointer.toNat → post.memory address = state.memory address) :
    ExtensionChildrenIn live extensions post := by
  intro node member child loaded
  have bound := headers node member
  have nextNat : (node + (48 : BitVec 64)).toNat = node.toNat + 48 := by
    rw [BitVec.toNat_add_of_lt (by have limit := pointer.isLt; change node.toNat + 48 < 2^64; omega)]
    rfl
  have before : (node + (48 : BitVec 64)).toNat < pointer.toNat := by rw [nextNat]; omega
  exact children node member child ((frame _ before).symm.trans loaded)

#print axioms extensionChildrenIn_empty
#print axioms ExtensionChildrenIn.mono
#print axioms extensionChildrenIn_before_frame
end InitECandidate.Runtime
