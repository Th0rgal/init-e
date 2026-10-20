import InitECandidate.Runtime.AllocatedTrieWorld
import InitECandidate.Runtime.TrieNodeMetadataStore
namespace InitECandidate.Runtime
open Flapjack Flapjack.PanSemStateFiniteExact

theorem AllocatedTrieWorld.after_memory_globals {F : Type}
 {s post : PanSemStateFiniteExact 64 F} {live extensions branches : Set (BitVec 64)}
 {size : BitVec 64 → Nat} {frontier : BitVec 64}
 (world : AllocatedTrieWorld s live extensions branches size frontier)
 (memory : post.memory=s.memory) (globals : post.globals=s.globals) :
 AllocatedTrieWorld post live extensions branches size frontier := by
 refine ⟨world.registry.after_memory memory,world.positive.after_length_frame ?_,world.layout,world.allocated,?_,world.capped,world.aligned⟩
 · intro node member;rw [memory]
 · rw [globals];exact world.heap

theorem AllocatedTrieWorld.write_metadata {F : Type} {s : PanSemStateFiniteExact 64 F}
 {live extensions branches : Set (BitVec 64)} {size : BitVec 64 → Nat} {frontier : BitVec 64}
 (world : AllocatedTrieWorld s live extensions branches size frontier)
 (parent value : BitVec 64) (member : parent∈live) (capacity : 32≤size parent)
 (offset : Nat) (positive : 0<offset) (small : offset<32) :
 AllocatedTrieWorld (sourceWriteWord s (parent+BitVec.ofNat 64 offset) value)
  live extensions branches size frontier := by
 have registry:=world.registry.write_metadata s live extensions branches size world.layout parent value member capacity offset positive small
 have kept : TriePositiveExtensions extensions (sourceWriteWord s (parent+BitVec.ofNat 64 offset) value) := by
  apply world.positive.after_length_frame
  intro node registered
  have separate:=world.layout.fields_ne node parent (world.layout.extensionLive registered) member
   40 offset (by have:=world.layout.extensionSize node registered;omega) (by omega) (Or.inr (by omega))
  change (sourceWriteWord s (parent+BitVec.ofNat 64 offset) value).memory (node+40#64)=s.memory (node+40#64)
  simp [sourceWriteWord,separate]
 exact ⟨registry,kept,world.layout,world.allocated,world.heap,world.capped,world.aligned⟩

#print axioms AllocatedTrieWorld.after_memory_globals
#print axioms AllocatedTrieWorld.write_metadata
end InitECandidate.Runtime
