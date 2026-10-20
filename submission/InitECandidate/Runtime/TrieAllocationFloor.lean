import InitECandidate.Runtime.TrieExternalWordStore
namespace InitECandidate.Runtime
open Flapjack Flapjack.PanSemStateFiniteExact

/-- Both allocated node records and their stored key buffers follow the
trie's earlier header allocation. This supplements record disjointness. -/
structure TrieAllocationFloor {F : Type} (s : PanSemStateFiniteExact 64 F)
 (live branches : Set (BitVec 64)) (floor : Nat) : Prop where
 records : ∀node∈live,floor≤node.toNat
 keys : ∀node∈live,node∉branches→∀key len : BitVec 64,
  s.memory (node+32)=.word key→s.memory (node+40)=.word len→floor≤key.toNat

theorem TrieAllocationFloor.empty {F : Type} (s : PanSemStateFiniteExact 64 F) (floor : Nat) :
 TrieAllocationFloor s ∅ ∅ floor := by
 constructor <;>intro node member <;>exact False.elim member

/-- Alignment of the allocation floor bounds the real containing word cell,
including when the stored path begins in the middle of a word. -/
theorem trie_path_cell_above_floor (key len : BitVec 64) (floor offset : Nat)
 (aligned : floor%8=0) (lower : floor≤key.toNat)
 (extent : key.toNat+len.toNat≤2^64) (inside : offset<len.toNat) :
 floor≤(panByteAlignHOL (key+BitVec.ofNat 64 offset)).toNat := by
 have lenBound:=len.isLt
 have natural : (key+BitVec.ofNat 64 offset).toNat=key.toNat+offset := by
  rw [BitVec.toNat_add,BitVec.toNat_ofNat]
  omega
 rw [panByteAlign_toNat64,natural]
 omega

/-- A header word below the aligned allocation floor is external to all
records and actual stored path cells, exactly as required by its root store. -/
theorem TrieAllocationFloor.external_word {F : Type} {s : PanSemStateFiniteExact 64 F}
 {live extensions branches : Set (BitVec 64)} {size : BitVec 64→Nat} {frontier : BitVec 64} {floor : Nat}
 (lower : TrieAllocationFloor s live branches floor)
 (paths : TrieNodePaths s live extensions branches size frontier)
 (aligned : floor%8=0) (address : BitVec 64) (before : address.toNat<floor) :
 TrieExternalWord s live branches address := by
 refine ⟨fun node member=>Nat.lt_of_lt_of_le before (lower.records node member),?_⟩
 intro node member nonBranch key len keyAt lenAt offset inside
 obtain ⟨actualKey,actualLen,storedKey,storedLen,_,path⟩:=paths.paths node member nonBranch
 have keyEq : actualKey=key:=HolWordLab.word.inj (storedKey.symm.trans keyAt)
 have lenEq : actualLen=len:=HolWordLab.word.inj (storedLen.symm.trans lenAt)
 rw [keyEq,lenEq] at path
 have extent : key.toNat+len.toNat≤2^64:=by have:=path.extent;have:=frontier.isLt;omega
 have cellBound:=trie_path_cell_above_floor key len floor offset aligned
  (lower.keys node member nonBranch key len keyAt lenAt) extent inside
 intro equal
 rw [equal] at cellBound
 omega

#print axioms TrieAllocationFloor.empty
#print axioms trie_path_cell_above_floor
#print axioms TrieAllocationFloor.external_word
end InitECandidate.Runtime
