import InitECandidate.Runtime.TrieOwnedFootprint
import InitECandidate.Runtime.TrieAllocationFloorStore
namespace InitECandidate.Runtime
open Flapjack Flapjack.PanSemStateFiniteExact

/-- One packaged separation and one explicit execution effect preserve all
four trie invariants. Non-memory context facts stay visible at the call site. -/
theorem trieScratch_preserves {F : Type} {s post : PanSemStateFiniteExact 64 F}
 {live extensions branches : Set (BitVec 64)} {size : BitVec 64→Nat}
 {frontier : BitVec 64} {floor : Nat} {scratch : Set (BitVec 64)}
 (world : AllocatedTrieWorld s live extensions branches size frontier)
 (kinds : TrieNodeKinds s live extensions branches)
 (paths : TrieNodePaths s live extensions branches size frontier)
 (lower : TrieAllocationFloor s live branches floor)
 (owned : (trieScratch s.memory live branches size scratch).holds s.memory)
 (effect : WordSep.WritesOnly scratch s.memory post.memory)
 (globals : post.globals=s.globals) (domain : post.memaddrs=s.memaddrs) (endian : post.be=s.be) :
 AllocatedTrieWorld post live extensions branches size frontier ∧TrieNodeKinds post live extensions branches ∧
 TrieNodePaths post live extensions branches size frontier ∧TrieAllocationFloor post live branches floor := by
 have kept:=trieScratch_frame owned effect
 exact ⟨world.after_owned_frame kept globals,kinds.after_owned_frame world kept,
  paths.after_owned_frame world kept domain endian,lower.after_owned_frame paths world kept⟩

#print axioms trieScratch_preserves

/-- A concrete store into the packaged scratch region supplies its actual
write effect. The same separation witness transports both trie invariants. -/
theorem trieScratch_write_word {F : Type} {s : PanSemStateFiniteExact 64 F}
 {live extensions branches : Set (BitVec 64)} {size : BitVec 64→Nat}
 {frontier : BitVec 64} {floor : Nat} {scratch : Set (BitVec 64)}
 (world : AllocatedTrieWorld s live extensions branches size frontier)
 (kinds : TrieNodeKinds s live extensions branches)
 (paths : TrieNodePaths s live extensions branches size frontier)
 (lower : TrieAllocationFloor s live branches floor)
 (owned : (trieScratch s.memory live branches size scratch).holds s.memory)
 (address value : BitVec 64) (inside : address∈scratch) :
 AllocatedTrieWorld (sourceWriteWord s address value) live extensions branches size frontier ∧
 TrieNodeKinds (sourceWriteWord s address value) live extensions branches ∧
 TrieNodePaths (sourceWriteWord s address value) live extensions branches size frontier ∧
 TrieAllocationFloor (sourceWriteWord s address value) live branches floor := by
 have effect : WordSep.WritesOnly scratch s.memory (sourceWriteWord s address value).memory := by
  intro watched outside
  have different : watched≠address:=by intro same;exact outside (same ▸ inside)
  simp [sourceWriteWord,different]
 exact trieScratch_preserves world kinds paths lower owned effect rfl rfl rfl

#print axioms trieScratch_write_word
end InitECandidate.Runtime
