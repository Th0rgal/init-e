import InitECandidate.Runtime.TrieNodePaths
namespace InitECandidate.Runtime
open Flapjack Flapjack.PanSemStateFiniteExact

/-- Lexical scope and clock restoration keep stored path facts when the
actual memory, domain and endianness are unchanged. -/
theorem TriePathBuffer.after_context {F : Type} {s post : PanSemStateFiniteExact 64 F}
 {live : Set (BitVec 64)} {size : BitVec 64 → Nat} {key length frontier : BitVec 64}
 (path : TriePathBuffer s live size key length frontier)
 (memory : post.memory=s.memory) (domain : post.memaddrs=s.memaddrs) (endian : post.be=s.be) :
 TriePathBuffer post live size key length frontier :=
 ⟨path.nibbles.after_frame memory domain endian,path.extent,path.separate⟩

theorem TrieNodePaths.after_context {F : Type} {s post : PanSemStateFiniteExact 64 F}
 {live extensions branches : Set (BitVec 64)} {size : BitVec 64 → Nat} {frontier : BitVec 64}
 (paths : TrieNodePaths s live extensions branches size frontier)
 (memory : post.memory=s.memory) (domain : post.memaddrs=s.memaddrs) (endian : post.be=s.be) :
 TrieNodePaths post live extensions branches size frontier := by
 refine ⟨paths.leafCapacity,?_⟩
 intro node member nonBranch
 obtain ⟨key,len,keyAt,lenAt,short,path⟩:=paths.paths node member nonBranch
 exact ⟨key,len,by rw [memory];exact keyAt,by rw [memory];exact lenAt,short,path.after_context memory domain endian⟩

#print axioms TriePathBuffer.after_context
#print axioms TrieNodePaths.after_context
end InitECandidate.Runtime
