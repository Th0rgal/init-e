import InitECandidate.Runtime.WordSeparation
import InitECandidate.Runtime.TriePathBuffer
import InitECandidate.Runtime.NodeInvalidateNibbleWorld
namespace InitECandidate.Runtime
open Flapjack Flapjack.PanSemStateFiniteExact

/-- Frame the stored path's actual containing cells against a node-field
write footprint. This is shared by payload, cache and child-link updates. -/
theorem TriePathBuffer.after_record_fields {F : Type} {s post : PanSemStateFiniteExact 64 F}
 {live extensions branches : Set (BitVec 64)} {size : BitVec 64→Nat} {frontier key len : BitVec 64}
 (path : TriePathBuffer s live size key len frontier)
 (world : AllocatedTrieWorld s live extensions branches size frontier)
 (node : BitVec 64) (member : node∈live) (fields : List Nat)
 (inside : ∀field∈fields,field<size node)
 (frame : ∀watched : BitVec 64,(∀field∈fields,watched≠node+BitVec.ofNat 64 field)→post.memory watched=s.memory watched)
 (domain : post.memaddrs=s.memaddrs) (endian : post.be=s.be) :
 TriePathBuffer post live size key len frontier := by
 let writes : Set WordSep.Address:={a|∃field∈fields,a=node+BitVec.ofNat 64 field}
 let reads : Set WordSep.Address:={a|∃offset : Nat,offset<len.toNat ∧a=panByteAlignHOL (key+BitVec.ofNat 64 offset)}
 have effect : WordSep.WritesOnly writes s.memory post.memory := by
  intro address outside
  apply frame
  intro field included equal
  exact outside ⟨field,included,equal⟩
 have separate : Disjoint writes reads := by
  apply Set.disjoint_left.mpr
  intro address ⟨field,included,atField⟩ ⟨offset,small,atCell⟩
  have natural:=congrArg BitVec.toNat (atCell.symm.trans atField)
  rw [world.layout.field_nat node member field (inside field included)] at natural
  have fieldInside:=inside field included
  rcases path.separate offset small node member with before|after <;>omega
 have kept : (WordSep.snapshot reads s.memory).holds post.memory :=
  WordSep.frame _ effect separate (by intro address owned;rfl)
 have nibbles : TrieNibbleRange post key len := by
  apply path.nibbles.after_cells _ domain endian
  intro offset small
  exact kept _ ⟨offset,small,rfl⟩
 exact ⟨nibbles,path.extent,path.separate⟩

#print axioms TriePathBuffer.after_record_fields
end InitECandidate.Runtime
