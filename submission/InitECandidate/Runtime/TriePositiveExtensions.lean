import InitECandidate.Runtime.FreshTrieRegistryWordBounds
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- Indexed insertion constructs only positive-length extensions. This stronger
invariant permits a child link to be replaced by a newer allocation without
requiring the new child address to precede its parent. -/
def TriePositiveExtensions {F : Type} (extensions : Set (BitVec 64))
 (state : PanSemStateFiniteExact 64 F) : Prop :=
 ∀ node ∈ extensions, ∃ length : BitVec 64,
  state.memory (node+40)=.word length ∧ length≠0

theorem TriePositiveExtensions.empty {F : Type} (s : PanSemStateFiniteExact 64 F) :
 TriePositiveExtensions ∅ s := by
 intro node member
 exact False.elim member

theorem TriePositiveExtensions.after_length_frame {F : Type}
 {s post : PanSemStateFiniteExact 64 F} {extensions : Set (BitVec 64)}
 (positive : TriePositiveExtensions extensions s)
 (frame : ∀ node∈extensions,post.memory (node+40)=s.memory (node+40)) :
 TriePositiveExtensions extensions post := by
 intro node member
 obtain ⟨length,loaded,nonzero⟩:=positive node member
 exact ⟨length,(frame node member).trans loaded,nonzero⟩

theorem TriePositiveExtensions.order {F : Type}
 {s : PanSemStateFiniteExact 64 F} {extensions : Set (BitVec 64)}
 (positive : TriePositiveExtensions extensions s) : ExtensionOrderFamily extensions s := by
 intro node member child zero loaded
 obtain ⟨length,atLength,nonzero⟩:=positive node member
 exact False.elim (nonzero (HolWordLab.word.inj (atLength.symm.trans zero)))

theorem TriePositiveExtensions.after_registry_word_frame {F : Type}
 {s post : PanSemStateFiniteExact 64 F} {live extensions branches : Set (BitVec 64)}
 (positive : TriePositiveExtensions extensions s)
 (frame : ∀ address,TrieWalkRegistryWord live extensions branches address→post.memory address=s.memory address) :
 TriePositiveExtensions extensions post :=
 positive.after_length_frame (fun node member=>frame _ (Or.inr (Or.inl ⟨node,member,Or.inl rfl⟩)))

theorem NodeNewLeafDeclarationReady.positive_extensions {F : Type}
 {s post : PanSemStateFiniteExact 64 F} {name : MlS}
 {pointer nib length valuePointer valueLength : BitVec 64} {live extensions branches : Set (BitVec 64)}
 (ready : NodeNewLeafDeclarationReady s post name pointer nib length valuePointer valueLength live extensions branches)
 (positive : TriePositiveExtensions extensions s)
 (below : ∀ address,TrieWalkRegistryWord live extensions branches address→address.toNat<pointer.toNat) :
 TriePositiveExtensions extensions post :=
 positive.after_length_frame (fun node member=>ready.memory _ (below _ (Or.inr (Or.inl ⟨node,member,Or.inl rfl⟩))))

theorem NodeNewBranchDeclarationReady.positive_extensions {F : Type}
 {s post : PanSemStateFiniteExact 64 F} {name : MlS}
 {pointer : BitVec 64} {live extensions branches : Set (BitVec 64)}
 (ready : NodeNewBranchDeclarationReady s post name pointer live extensions branches)
 (positive : TriePositiveExtensions extensions s)
 (below : ∀ address,TrieWalkRegistryWord live extensions branches address→address.toNat<pointer.toNat) :
 TriePositiveExtensions extensions post :=
 positive.after_length_frame (fun node member=>ready.memory _ (below _ (Or.inr (Or.inl ⟨node,member,Or.inl rfl⟩))))

theorem NodeNewExtDeclarationReady.positive_extensions {F : Type}
 {s post : PanSemStateFiniteExact 64 F} {name : MlS}
 {pointer nib length child : BitVec 64} {live extensions branches : Set (BitVec 64)}
 (ready : NodeNewExtDeclarationReady s post name pointer nib length child live extensions branches)
 (positive : TriePositiveExtensions extensions s) (nonzero : length≠0)
 (below : ∀ address,TrieWalkRegistryWord live extensions branches address→address.toNat<pointer.toNat) :
 TriePositiveExtensions (insert pointer extensions) post := by
 have older:=positive.after_length_frame (fun node member=>ready.memory _
  (below _ (Or.inr (Or.inl ⟨node,member,Or.inl rfl⟩))))
 intro node member
 rcases member with fresh|old
 · subst node
   exact ⟨length,ready.lengthAt,nonzero⟩
 · exact older node old

#print axioms TriePositiveExtensions.order
#print axioms NodeNewLeafDeclarationReady.positive_extensions
#print axioms NodeNewBranchDeclarationReady.positive_extensions
#print axioms NodeNewExtDeclarationReady.positive_extensions
end InitECandidate.Runtime
