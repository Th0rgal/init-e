import InitECandidate.Runtime.TrieFreshAllocationFloor
import InitECandidate.Runtime.TrieNodePathsFrame
namespace InitECandidate.Runtime
open Flapjack Flapjack.PanSemStateFiniteExact

/-- Actual record-field updates that do not replace stored path headers preserve
both allocation floors. A branch may update any of its own child fields. -/
theorem TrieAllocationFloor.after_record_fields {F : Type} {s post : PanSemStateFiniteExact 64 F}
 {live extensions branches : Set (BitVec 64)} {size : BitVec 64→Nat} {frontier : BitVec 64} {floor : Nat}
 (lower : TrieAllocationFloor s live branches floor)
 (paths : TrieNodePaths s live extensions branches size frontier)
 (world : AllocatedTrieWorld s live extensions branches size frontier)
 (parent : BitVec 64) (member : parent∈live) (fields : List Nat)
 (inside : ∀field∈fields,field<size parent)
 (headerSafe : parent∈branches ∨∀field∈fields,field≠32 ∧field≠40)
 (frame : ∀watched : BitVec 64,(∀field∈fields,watched≠parent+BitVec.ofNat 64 field)→post.memory watched=s.memory watched) :
 TrieAllocationFloor post live branches floor := by
 refine ⟨lower.records,?_⟩
 intro node registered nonBranch key len keyAt lenAt
 have headerFrame := paths.stored_header_frame world parent member fields inside headerSafe frame node registered nonBranch
 apply lower.keys node registered nonBranch key len
 · exact (headerFrame 32 (Or.inl rfl)).symm.trans keyAt
 · exact (headerFrame 40 (Or.inr rfl)).symm.trans lenAt

/-- Slicing a real path inside its nonwrapping extent cannot move its start
below the original allocation floor. -/
theorem trie_path_slice_above_floor (key len : BitVec 64) (floor offset : Nat)
 (lower : floor≤key.toNat) (extent : key.toNat+len.toNat<2^64)
 (inside : offset≤len.toNat) : floor≤(key+BitVec.ofNat 64 offset).toNat := by
 rw [BitVec.toNat_add,BitVec.toNat_ofNat]
 have:=len.isLt
 omega

#print axioms TrieAllocationFloor.after_record_fields
#print axioms trie_path_slice_above_floor
end InitECandidate.Runtime
