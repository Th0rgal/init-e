import InitECandidate.Runtime.NodedbSetValues
import InitECandidate.Runtime.RlpSliceInputPrefix
namespace InitECandidate.Runtime
open Flapjack Flapjack.PanSemStateFiniteExact
/-- Empty source databases have no possible live slice targets; their unused
array pointer can be placed at the current heap without changing database facts. -/
theorem nodedb_empty_slice_retarget {F : Type} (s : PanSemStateFiniteExact 64 F)
 (table array replacement count input length : BitVec 64)
 (empty : count=0) (entries : HashTableValuesIn table (NodedbSliceTargets array count) s) :
 HashTableValuesIn table (NodedbSliceTargets replacement count) s ∧
 RlpSliceInputPrefix s replacement input length count.toNat := by
 constructor
 · apply entries.mono
   intro value member
   obtain ⟨index,inside,_⟩ := member
   simp [empty] at inside
 · intro index inside
   simp [empty] at inside
#print axioms nodedb_empty_slice_retarget
end InitECandidate.Runtime
