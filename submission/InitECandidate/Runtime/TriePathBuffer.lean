import InitECandidate.Runtime.TrieNibbleAllocationFrame
import InitECandidate.Runtime.AllocatedTrieChildKinds
namespace InitECandidate.Runtime
open Flapjack Flapjack.PanSemStateFiniteExact

/-- A stored path has real nibble bytes, lies before the heap frontier and
its containing word cells avoid every allocated node record. Slices need
not remain aligned, so separation is stated on the actual containing cells. -/
structure TriePathBuffer {F : Type} (s : PanSemStateFiniteExact 64 F)
 (live : Set (BitVec 64)) (size : BitVec 64 → Nat) (key length frontier : BitVec 64) : Prop where
 nibbles : TrieNibbleRange s key length
 extent : key.toNat+length.toNat≤frontier.toNat
 separate : ∀offset : Nat,offset<length.toNat→∀node∈live,
  (panByteAlignHOL (key+BitVec.ofNat 64 offset)).toNat<node.toNat ∨
  node.toNat+size node≤(panByteAlignHOL (key+BitVec.ofNat 64 offset)).toNat

/-- Any concrete node-field store preserves all bytes of a separate stored
path, including a path slice starting in the middle of a word. -/
theorem TriePathBuffer.after_node_field {F : Type} {s : PanSemStateFiniteExact 64 F}
 {live extensions branches : Set (BitVec 64)} {size : BitVec 64 → Nat} {key length frontier : BitVec 64}
 (path : TriePathBuffer s live size key length frontier)
 (layout : TrieNodeLayout live extensions branches size)
 (node value : BitVec 64) (member : node∈live) (field : Nat) (inside : field<size node) :
 TriePathBuffer (sourceWriteWord s (node+BitVec.ofNat 64 field) value) live size key length frontier := by
 refine ⟨path.nibbles.after_word_outside _ value ?_,path.extent,path.separate⟩
 intro offset small equal
 have natural:=congrArg BitVec.toNat equal
 rw [layout.field_nat node member field inside] at natural
 rcases path.separate offset small node member with before|after <;> omega

/-- The indexed path remains separate from a fresh record and retains its
actual bytes when allocation writes only at/above the previous frontier. -/
theorem TriePathBuffer.after_new_record {F : Type} {s post : PanSemStateFiniteExact 64 F}
 {live extensions branches : Set (BitVec 64)} {size : BitVec 64 → Nat} {key length frontier next : BitVec 64}
 (path : TriePathBuffer s live size key length frontier)
 (world : AllocatedTrieWorld s live extensions branches size frontier)
 (recordSize : Nat) (grown : frontier.toNat≤next.toNat)
 (memory : ∀address : BitVec 64,address.toNat<frontier.toNat→post.memory address=s.memory address)
 (domain : post.memaddrs=s.memaddrs) (endian : post.be=s.be) :
 TriePathBuffer post (insert frontier live) (Function.update size frontier recordSize) key length next := by
 have extent:=path.extent
 refine ⟨path.nibbles.before_allocation frontier path.extent memory domain endian,by omega,?_⟩
 intro offset small node member
 have atByte : (key+BitVec.ofNat 64 offset).toNat=key.toNat+offset := by
  rw [BitVec.toNat_add,BitVec.toNat_ofNat]
  have:=frontier.isLt
  omega
 have below : (panByteAlignHOL (key+BitVec.ofNat 64 offset)).toNat<frontier.toNat := by
  rw [panByteAlign_toNat64,atByte]
  have:=Nat.div_mul_le_self (key.toNat+offset) 8
  omega
 rcases member with fresh|old
 · subst node;exact Or.inl below
 · have different : node≠frontier := by
    intro same;subst node
    have:=world.layout.positive frontier old
    have:=world.allocated frontier old
    omega
   simpa [Function.update_of_ne different] using path.separate offset small node old

#print axioms TriePathBuffer.after_node_field
#print axioms TriePathBuffer.after_new_record
end InitECandidate.Runtime
