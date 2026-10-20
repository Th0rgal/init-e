import InitECandidate.Runtime.TriePayloadWordsFrame
import InitECandidate.Runtime.FreshTrieNodePaths
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact

/-- The actual leaf constructor supplies word-valued payloads and retains all
old leaf/branch payload words through its real below-frontier frame. -/
theorem NodeNewLeafDeclarationReady.payload_words {F : Type}
 {s post : PanSemStateFiniteExact 64 F} {name : MlS}
 {pointer nib length value valueLength : BitVec 64}
 {live extensions branches : Set (BitVec 64)} {size : BitVec 64→Nat}
 (ready : NodeNewLeafDeclarationReady s post name pointer nib length value valueLength live extensions branches)
 (world : AllocatedTrieWorld s live extensions branches size pointer)
 (paths : TrieNodePaths s live extensions branches size pointer)
 (valid : TriePayloadWords s live extensions branches) :
 TriePayloadWords post (insert pointer live) extensions branches := by
 have older:=valid.after_below_frame world paths ready.memory
 constructor
 · intro node member nonExt nonBranch
   rcases member with fresh|old
   · subst node
     exact ⟨⟨value,ready.valueAt⟩,⟨valueLength,ready.valueLengthAt⟩⟩
   · exact older.leaf node old nonExt nonBranch
 · exact older.branch

/-- A new extension adds no leaf payload and retains all old payload words. -/
theorem NodeNewExtDeclarationReady.payload_words {F : Type}
 {s post : PanSemStateFiniteExact 64 F} {name : MlS}
 {pointer nib length child : BitVec 64}
 {live extensions branches : Set (BitVec 64)} {size : BitVec 64→Nat}
 (ready : NodeNewExtDeclarationReady s post name pointer nib length child live extensions branches)
 (world : AllocatedTrieWorld s live extensions branches size pointer)
 (paths : TrieNodePaths s live extensions branches size pointer)
 (valid : TriePayloadWords s live extensions branches) :
 TriePayloadWords post (insert pointer live) (insert pointer extensions) branches := by
 have older:=valid.after_below_frame world paths ready.memory
 constructor
 · intro node member nonExt nonBranch
   rcases member with fresh|old
   · subst node;exact False.elim (nonExt (Or.inl rfl))
   · exact older.leaf node old (fun member=>nonExt (Or.inr member)) nonBranch
 · exact older.branch

#print axioms NodeNewLeafDeclarationReady.payload_words
#print axioms NodeNewExtDeclarationReady.payload_words
end InitECandidate.Runtime
