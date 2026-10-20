import InitECandidate.Runtime.TriePositiveExtensions
import InitECandidate.Runtime.TrieNodeLayout
namespace InitECandidate.Runtime
open Flapjack Flapjack.PanSemStateFiniteExact

/-- For constructed positive extensions, replacing a child with a newer
allocation needs no address-decrease premise. Only the unchanged length and
kind fields, and the new child's membership, are required. -/
theorem TrieWalkRegistry.write_positive_child {F : Type}
 (state : PanSemStateFiniteExact 64 F) (live extensions branches : Set (BitVec 64))
 (address child : BitVec 64) (registry : TrieWalkRegistry live extensions branches state)
 (positive : TriePositiveExtensions extensions state)
 (childValid : child=0 ∨child∈live)
 (kindsSeparate : ∀node∈live,node≠address)
 (lengthsSeparate : ∀node∈extensions,node+40≠address) :
 TrieWalkRegistry live extensions branches (sourceWriteWord state address child) ∧
 TriePositiveExtensions extensions (sourceWriteWord state address child) := by
 constructor
 · apply registry.write_child state live extensions branches address child childValid kindsSeparate lengthsSeparate
   intro node member same zero
   obtain ⟨length,loaded,nonzero⟩:=positive node member
   exact False.elim (nonzero (HolWordLab.word.inj (loaded.symm.trans zero)))
 · apply positive.after_length_frame
   intro node member
   have separate : node+40#64≠address := lengthsSeparate node member
   simp [sourceWriteWord,separate]

theorem TrieWalkRegistry.write_positive_branch_slot {F : Type}
 (state : PanSemStateFiniteExact 64 F) (live extensions branches : Set (BitVec 64))
 (size : BitVec 64 → Nat) (layout : TrieNodeLayout live extensions branches size)
 (registry : TrieWalkRegistry live extensions branches state)
 (positive : TriePositiveExtensions extensions state)
 (parent child : BitVec 64) (registered : parent∈branches) (slot : Nat) (small : slot<16)
 (childValid : child=0 ∨child∈live) :
 TrieWalkRegistry live extensions branches (sourceWriteWord state (branchChildAddress parent slot) child) ∧
 TriePositiveExtensions extensions (sourceWriteWord state (branchChildAddress parent slot) child) := by
 obtain ⟨kinds,lengths,_⟩:=layout.branch_slot_separate parent registered slot small
 exact registry.write_positive_child state live extensions branches _ child positive childValid kinds lengths

#print axioms TrieWalkRegistry.write_positive_child
#print axioms TrieWalkRegistry.write_positive_branch_slot
end InitECandidate.Runtime
