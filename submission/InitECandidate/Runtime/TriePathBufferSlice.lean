import InitECandidate.Runtime.TriePathBuffer
namespace InitECandidate.Runtime
open Flapjack Flapjack.PanSemStateFiniteExact

/-- The actual pointer/length slices used by leaf and extension splitting
inherit both nibble validity and separation of their containing word cells. -/
theorem TriePathBuffer.slice {F : Type} {s : PanSemStateFiniteExact 64 F}
 {live : Set (BitVec 64)} {size : BitVec 64 → Nat} {key length frontier start count : BitVec 64}
 (path : TriePathBuffer s live size key length frontier)
 (bounded : start.toNat+count.toNat≤length.toNat) :
 TriePathBuffer s live size (key+start) count frontier := by
 have extent:=path.extent
 have shifted : (key+start).toNat=key.toNat+start.toNat := by
  rw [BitVec.toNat_add]
  have:=frontier.isLt
  omega
 refine ⟨path.nibbles.slice bounded,by rw [shifted];omega,?_⟩
 intro offset small node member
 have combined : (key+start)+BitVec.ofNat 64 offset=key+BitVec.ofNat 64 (start.toNat+offset) := by
  simp [BitVec.ofNat_add,BitVec.add_assoc]
 rw [combined]
 exact path.separate (start.toNat+offset) (by omega) node member

/-- In particular the suffix after a matched common prefix stays valid and
separate; subtraction follows the real non-wrapping source length. -/
theorem TriePathBuffer.suffix {F : Type} {s : PanSemStateFiniteExact 64 F}
 {live : Set (BitVec 64)} {size : BitVec 64 → Nat} {key length frontier start : BitVec 64}
 (path : TriePathBuffer s live size key length frontier) (bounded : start.toNat≤length.toNat) :
 TriePathBuffer s live size (key+start) (length-start) frontier := by
 apply path.slice
 rw [BitVec.toNat_sub_of_le (BitVec.le_def.mpr bounded)]
 omega

#print axioms TriePathBuffer.slice
#print axioms TriePathBuffer.suffix
end InitECandidate.Runtime
