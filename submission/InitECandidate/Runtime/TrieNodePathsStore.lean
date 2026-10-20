import InitECandidate.Runtime.TrieNodePaths
namespace InitECandidate.Runtime
open Flapjack Flapjack.PanSemStateFiniteExact

/-- Real node updates preserve stored paths when they avoid the two segment
header offsets. Branch child slots may use those offsets: branches have no
segment header, and every other record is physically separate. -/
theorem TrieNodePaths.after_node_field {F : Type} {s : PanSemStateFiniteExact 64 F}
 {live extensions branches : Set (BitVec 64)} {size : BitVec 64 → Nat} {frontier : BitVec 64}
 (paths : TrieNodePaths s live extensions branches size frontier)
 (world : AllocatedTrieWorld s live extensions branches size frontier)
 (parent value : BitVec 64) (member : parent∈live) (field : Nat) (inside : field<size parent)
 (headerSafe : parent∈branches ∨(field≠32 ∧field≠40)) :
 TrieNodePaths (sourceWriteWord s (parent+BitVec.ofNat 64 field) value) live extensions branches size frontier := by
 have headers (node : BitVec 64) (registered : node∈live) (nonBranch : node∉branches)
  (offset : Nat) (atHeader : offset=32 ∨offset=40) :
  node+BitVec.ofNat 64 offset≠parent+BitVec.ofNat 64 field := by
  have headerInside : offset<size node := by
   have capacity:=paths.header_capacity world.layout node registered nonBranch
   rcases atHeader with rfl|rfl <;> omega
  apply world.layout.fields_ne node parent registered member offset field headerInside inside
  by_cases same : node=parent
  · subst node
    right
    rcases headerSafe with branch|⟨not32,not40⟩
    · exact False.elim (nonBranch branch)
    · rcases atHeader with rfl|rfl
      · exact Ne.symm not32
      · exact Ne.symm not40
  · exact Or.inl same
 refine ⟨paths.leafCapacity,?_⟩
 intro node registered nonBranch
 obtain ⟨key,len,keyAt,lenAt,small,path⟩:=paths.paths node registered nonBranch
 have keyAtTyped : s.memory (node+32#64)=.word key:=keyAt
 have lenAtTyped : s.memory (node+40#64)=.word len:=lenAt
 refine ⟨key,len,?_,?_,small,path.after_node_field world.layout parent value member field inside⟩
 · change (sourceWriteWord s (parent+BitVec.ofNat 64 field) value).memory (node+BitVec.ofNat 64 32)=_
   simp [sourceWriteWord,headers node registered nonBranch 32 (Or.inl rfl),keyAtTyped]
 · change (sourceWriteWord s (parent+BitVec.ofNat 64 field) value).memory (node+BitVec.ofNat 64 40)=_
   simp [sourceWriteWord,headers node registered nonBranch 40 (Or.inr rfl),lenAtTyped]

#print axioms TrieNodePaths.after_node_field
end InitECandidate.Runtime
