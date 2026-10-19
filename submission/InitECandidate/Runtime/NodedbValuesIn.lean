import InitECandidate.Runtime.NodedbDecodedReturnedValues
namespace InitECandidate.Runtime
open Flapjack Flapjack.PanSemStateFiniteExact

/-- The constructor/insertion membership invariant yields the header-indexed
property consumed by lookup, without choosing a different table layout. -/
theorem VTabs.values_in {F : Type} (s : PanSemStateFiniteExact 64 F)
    (targets : Set (BitVec 64))
    (keyLength table keys stride capacity used values order orderPos count : BitVec 64) (bits : Nat)
    (inv : HtabAligned keyLength table keys stride capacity used values order orderPos count bits s)
    (vt : VTabs targets s capacity count used keys stride values order) :
    HashTableValuesIn table targets s := by
  intro otherCapacity otherUsed otherValues capCell usedCell valueCell
  have capEq : otherCapacity = capacity := HolWordLab.word.inj (capCell.symm.trans inv.cell16)
  have usedEq : otherUsed = used := HolWordLab.word.inj (usedCell.symm.trans inv.cell48)
  have valuesEq : otherValues = values := HolWordLab.word.inj (valueCell.symm.trans inv.cell40)
  subst otherCapacity
  subst otherUsed
  subst otherValues
  exact vt.2.1

#print axioms VTabs.values_in
end InitECandidate.Runtime
