import ActualTaggedTrie
import InitECandidate.Runtime.WordSeparation

namespace BoundedTableExperiment

open InitECandidate.Runtime
open InitECandidate.Runtime.FineCost
open Flapjack
open Flapjack.PanSemStateFiniteExact
open InitECandidate.Runtime.WordSep

set_option maxHeartbeats 2000000

/-- Cells owned by tagged reachable node records. -/
def taggedNodeCells {F : Type} (s : PanSemStateFiniteExact 64 F)
    (cap root : BitVec 64) : Set Address :=
  {a | ∃ p, ReachableInternal s cap root p ∧ (a = p ∨ a = p + 8 ∨ a = p + 16)}

/-- Word cells of a path-buffer slot range. -/
def pathSlotCells (path : Address) (slots : Nat) : Set Address :=
  {a | ∃ i, i < slots ∧ a = path + BitVec.ofNat 64 (8 * i)}

/-- A one-word store whose address lies in the path slots, under disjointness
from tagged node cells, preserves the tagged trie invariant. -/
theorem tagged_store_frame {F : Type} {s : PanSemStateFiniteExact 64 F}
    {root cap : BitVec 64} {keyLen : Nat} (trie : TaggedTrieInv s root cap keyLen)
    {path : Address} {slots : Nat} {address : Address} {value : BitVec 64}
    {mem : Address → HolWordLab 64}
    (hdisj : Disjoint (pathSlotCells path slots) (taggedNodeCells s cap root))
    (hmem : address ∈ pathSlotCells path slots)
    (write : @panMemStoresHOL 64 _ address [.word value]
      s.memaddrs (Classical.decPred _) s.memory = some mem) :
    TaggedTrieInv { s with memory := mem } root cap keyLen := by
  have haddrNode : address ∉ taggedNodeCells s cap root := by
    intro hnode
    exact Set.disjoint_left.mp hdisj hmem hnode
  refine trie.store_other (.word value) write ?_
  intro p reach
  have hp : p ∈ taggedNodeCells s cap root := ⟨p, reach, Or.inl rfl⟩
  have hp8 : p + 8 ∈ taggedNodeCells s cap root := ⟨p, reach, Or.inr (Or.inl rfl)⟩
  have hp16 : p + 16 ∈ taggedNodeCells s cap root := ⟨p, reach, Or.inr (Or.inr rfl)⟩
  refine ⟨?_, ?_, ?_⟩
  · intro h
    exact haddrNode (h ▸ hp)
  · intro h
    exact haddrNode (h ▸ hp8)
  · intro h
    exact haddrNode (h ▸ hp16)

end BoundedTableExperiment

#print axioms BoundedTableExperiment.tagged_store_frame
