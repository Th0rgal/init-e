import InitECandidate.Runtime.MptSetIndexedPathPrefix
import InitECandidate.Runtime.TrieNodePaths
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact

/-- The actual indexed-key conversion preserves all older node keys and
exact kinds while advancing the heap past its new nibble buffer. -/
theorem MptNibbleUnsecuredDeclarationReady.stored_paths {F : Type}
 {s next : PanSemStateFiniteExact 64 F} {name : MlS} {pointer length : BitVec 64}
 (ready : MptNibbleUnsecuredDeclarationReady s next name pointer length)
 (live extensions branches : Set (BitVec 64)) (size : BitVec 64 → Nat)
 (world : AllocatedTrieWorld s live extensions branches size pointer)
 (kinds : TrieNodeKinds s live extensions branches)
 (paths : TrieNodePaths s live extensions branches size pointer) (short : length.toNat≤9) :
 TrieNodeKinds next live extensions branches ∧
 TrieNodePaths next live extensions branches size (allocationEnd pointer (2*length)) := by
 have before:=ready.before_memory short world.capped world.aligned
 have sum:=allocationGuard_sum_bound pointer (2*length) world.capped ready.2.2.2.1
 obtain ⟨cover,_,_⟩:=allocationEnd_covers pointer (2*length) sum
 have grown : pointer.toNat≤(allocationEnd pointer (2*length)).toNat:=by omega
 have domain : next.memaddrs=s.memaddrs:=ready.2.2.2.2.2.1
 have endian : next.be=s.be:=ready.2.2.2.2.2.2.1
 constructor
 · apply kinds.after_kind_frame world.layout.extensionLive world.layout.branchLive
   intro node member
   apply before
   have:=world.layout.positive node member
   have:=world.allocated node member
   omega
 · refine ⟨paths.leafCapacity,?_⟩
   intro node member nonBranch
   obtain ⟨key,len,keyAt,lenAt,small,path⟩:=paths.paths node member nonBranch
   have headerFrame (offset : Nat) (inside : offset<48) : next.memory (node+BitVec.ofNat 64 offset)=s.memory (node+BitVec.ofNat 64 offset) := by
    apply before
    have capacity:=paths.header_capacity world.layout node member nonBranch
    rw [world.layout.field_nat node member offset (by omega)]
    have:=world.allocated node member
    omega
   refine ⟨key,len,?_,?_,small,path.nibbles.before_allocation pointer path.extent before domain endian,?_,path.separate⟩
   · rw [show node+32=node+BitVec.ofNat 64 32 from rfl,headerFrame 32 (by decide)];exact keyAt
   · rw [show node+40=node+BitVec.ofNat 64 40 from rfl,headerFrame 40 (by decide)];exact lenAt
   · have extent:=path.extent;omega

#print axioms MptNibbleUnsecuredDeclarationReady.stored_paths
end InitECandidate.Runtime
