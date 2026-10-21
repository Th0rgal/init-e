import ActualTaggedTrie
import HeapFootprint
import CandidateFindLeafPush

namespace BoundedTableExperiment

open InitECandidate.Runtime
open InitECandidate.Runtime.FineCost
open Flapjack
open Flapjack.PanSemStateFiniteExact

set_option maxHeartbeats 2000000

/-- The concrete path-slot address is outside the node region once the path
buffer is disjoint from it and contains the current slot; consequently it is
different from each cell of a node record that lies wholly in the node
region. -/
theorem path_addr_avoids_node_cells (pbase psize nbase nsize depth : Nat)
    (hdisj : Disjoint pbase psize nbase nsize)
    (hpsize : (depth + 1) * 8 ≤ psize)
    (p : BitVec 64)
    (hp : InRegion nbase nsize p.toNat)
    (hp8 : InRegion nbase nsize (p + 8).toNat)
    (hp16 : InRegion nbase nsize (p + 16).toNat)
    (addr : BitVec 64) (haddrNat : addr.toNat = pbase + depth * 8) :
    p ≠ addr ∧ p + 8 ≠ addr ∧ p + 16 ≠ addr := by
  have hn : ¬ InRegion nbase nsize (pbase + depth * 8) :=
    (path_store_no_alias_all pbase psize nbase nsize nbase nsize nbase nsize
      nbase nsize depth
      { keys := hdisj, nodes := hdisj, output := hdisj, scratch := hdisj }
      hpsize).1
  refine ⟨?_, ?_, ?_⟩
  · intro h
    exact hn (by simpa [← haddrNat, h] using hp)
  · intro h
    have hnat : (p + 8).toNat = pbase + depth * 8 := by
      rw [congrArg BitVec.toNat h, haddrNat]
    exact hn (hnat ▸ hp8)
  · intro h
    have hnat : (p + 16).toNat = pbase + depth * 8 := by
      rw [congrArg BitVec.toNat h, haddrNat]
    exact hn (hnat ▸ hp16)

/-- The actual candidate path push preserves the tagged live-edge invariant
when the path buffer and node region are disjoint and every reachable node
record lies in the node region. -/
theorem candidateFindLeafPush_preserves_tagged {F : Type}
    {s : PanSemStateFiniteExact 64 F} {root cap : BitVec 64} {keyLen : Nat}
    (trie : TaggedTrieInv s root cap keyLen)
    {pbase psize nbase nsize depth : Nat}
    (hdisj : Disjoint pbase psize nbase nsize)
    (hpsize : (depth + 1) * 8 ≤ psize)
    (hcell : ∀ p, ReachableInternal s cap root p ->
      InRegion nbase nsize p.toNat ∧
      InRegion nbase nsize (p + 8).toNat ∧
      InRegion nbase nsize (p + 16).toNat)
    {address value : BitVec 64} {mem : BitVec 64 → HolWordLab 64}
    (haddr : address.toNat = pbase + depth * 8)
    (write : @panMemStoresHOL 64 _ address
      [.word value] s.memaddrs (Classical.decPred _) s.memory = some mem) :
    TaggedTrieInv { s with memory := mem } root cap keyLen := by
  refine trie.store_other (.word value) write ?_
  intro p reach
  obtain ⟨hp, hp8, hp16⟩ := hcell p reach
  exact path_addr_avoids_node_cells pbase psize nbase nsize depth hdisj hpsize
    p hp hp8 hp16 address haddr

end BoundedTableExperiment

#print axioms BoundedTableExperiment.path_addr_avoids_node_cells
#print axioms BoundedTableExperiment.candidateFindLeafPush_preserves_tagged
