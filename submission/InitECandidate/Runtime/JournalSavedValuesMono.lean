import InitECandidate.Runtime.JournalSavedValuesIn
namespace InitECandidate.Runtime
open Flapjack Flapjack.PanSemStateFiniteExact

/-- Enlarging the registry of permitted values preserves every saved undo value. -/
theorem JournalSavedValuesIn.mono_targets {F : Type} {journal : BitVec 64} {count : Nat}
    {watched targets larger : Set (BitVec 64)} {state : PanSemStateFiniteExact 64 F}
    (valid : JournalSavedValuesIn journal count watched targets state) (subset : targets ⊆ larger) :
    JournalSavedValuesIn journal count watched larger state := by
  intro index inside table present value t p v belongs occupied
  exact subset (valid index inside table present value t p v belongs occupied)

#print axioms JournalSavedValuesIn.mono_targets
end InitECandidate.Runtime
