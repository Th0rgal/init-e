import ActualSlabPathFrame
import ActualWordSepFrame

namespace BoundedTableExperiment

open InitECandidate.Runtime
open InitECandidate.Runtime.FineCost
open Flapjack
open Flapjack.PanSemStateFiniteExact
open InitECandidate.Runtime.WordSep

set_option maxHeartbeats 2000000

/-- Candidate heap invariant: tagged trie plus the actual node ownership in
the slab and the fresh path buffer placed after the slab. -/
structure CandidateHeapInv {F : Type} (s : PanSemStateFiniteExact 64 F)
    (root cap : BitVec 64) (keyLen : Nat)
    (base capN : Nat) (path : Address) (slots : Nat) (live free : List Nat) : Prop where
  trie : TaggedTrieInv s root cap keyLen
  owned : PtrOwned base capN live free
  liveReach : ∀ p, ReachableInternal s cap root p → p.toNat ∈ live
  pathEq : path.toNat = base + 24 * (capN / 2)
  pathBound : path.toNat ≤ 2 ^ 64
  nowrap : path.toNat + 8 * slots < 2 ^ 64

/-- Every tagged node cell is below the path buffer. -/
theorem CandidateHeapInv.nodeCellsBelow {F : Type} {s : PanSemStateFiniteExact 64 F}
    {root cap : BitVec 64} {keyLen : Nat}
    {base capN : Nat} {path : Address} {slots : Nat} {live free : List Nat}
    (inv : CandidateHeapInv s root cap keyLen base capN path slots live free) :
    ∀ b, b ∈ taggedNodeCells s cap root → b.toNat < path.toNat := by
  apply taggedNodeCells_below_of_slab
  · intro p reach
    exact inv.owned.partition.mem_iff.mp
      (List.mem_append.mpr (Or.inl (inv.liveReach p reach)))
  · exact inv.pathEq
  · exact inv.pathBound

/-- The path buffer and tagged node cells are disjoint. -/
theorem CandidateHeapInv.pathDisjoint {F : Type} {s : PanSemStateFiniteExact 64 F}
    {root cap : BitVec 64} {keyLen : Nat}
    {base capN : Nat} {path : Address} {slots : Nat} {live free : List Nat}
    (inv : CandidateHeapInv s root cap keyLen base capN path slots live free) :
    Disjoint (pathSlotCells path slots) (taggedNodeCells s cap root) :=
  pathSlotCells_disjoint_of_below path slots inv.nodeCellsBelow inv.nowrap

/-- The actual one-word path push preserves the candidate heap invariant. -/
theorem CandidateHeapInv.push {F : Type} {s : PanSemStateFiniteExact 64 F}
    {root cap : BitVec 64} {keyLen : Nat}
    {base capN : Nat} {path : Address} {slots : Nat} {live free : List Nat}
    (inv : CandidateHeapInv s root cap keyLen base capN path slots live free)
    {address : Address} {value : BitVec 64} {mem : Address → HolWordLab 64}
    (hmem : address ∈ pathSlotCells path slots)
    (write : @panMemStoresHOL 64 _ address [.word value]
      s.memaddrs (Classical.decPred _) s.memory = some mem) :
    CandidateHeapInv { s with memory := mem } root cap keyLen base capN path slots
      live free where
  trie := tagged_store_frame inv.trie inv.pathDisjoint hmem write
  owned := inv.owned
  liveReach := by
    intro p reachPost
    have haddrNode : address ∉ taggedNodeCells s cap root :=
      fun h => Set.disjoint_left.mp inv.pathDisjoint hmem h
    have reachPre := ReachableInternal.of_store_other (.word value) write
      (fun q hq => by
        refine ⟨?_, ?_, ?_⟩
        · intro h
          exact haddrNode (h ▸ ⟨q, hq, Or.inl rfl⟩)
        · intro h
          exact haddrNode (h ▸ ⟨q, hq, Or.inr (Or.inl rfl)⟩)
        · intro h
          exact haddrNode (h ▸ ⟨q, hq, Or.inr (Or.inr rfl)⟩)) reachPost
    exact inv.liveReach p reachPre
  pathEq := inv.pathEq
  pathBound := inv.pathBound
  nowrap := inv.nowrap

end BoundedTableExperiment

#print axioms BoundedTableExperiment.CandidateHeapInv.nodeCellsBelow
#print axioms BoundedTableExperiment.CandidateHeapInv.pathDisjoint
#print axioms BoundedTableExperiment.CandidateHeapInv.push
