import InitECandidate.Runtime.FreshTriePayloadWords
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact

/-- A concrete branch-ready state adds the two actual zero payload fields.
The source constructor endpoint proves these post-state word facts. -/
theorem NodeNewBranchDeclarationReady.payload_words {F : Type}
 {s post : PanSemStateFiniteExact 64 F} {name : MlS} {pointer : BitVec 64}
 {live extensions branches : Set (BitVec 64)} {size : BitVec 64→Nat}
 (ready : NodeNewBranchDeclarationReady s post name pointer live extensions branches)
 (world : AllocatedTrieWorld s live extensions branches size pointer)
 (paths : TrieNodePaths s live extensions branches size pointer)
 (valid : TriePayloadWords s live extensions branches)
 (valueAt : post.memory (pointer+160#64)=.word 0)
 (lengthAt : post.memory (pointer+168#64)=.word 0) :
 TriePayloadWords post (insert pointer live) extensions (insert pointer branches) := by
 have older:=valid.after_below_frame world paths ready.memory
 constructor
 · intro node member nonExt nonBranch
   rcases member with fresh|old
   · subst node;exact False.elim (nonBranch (Or.inl rfl))
   · exact older.leaf node old nonExt (fun member=>nonBranch (Or.inr member))
 · intro node member
   rcases member with fresh|old
   · subst node;exact ⟨⟨0,valueAt⟩,⟨0,lengthAt⟩⟩
   · exact older.branch node old

#print axioms NodeNewBranchDeclarationReady.payload_words
end InitECandidate.Runtime
