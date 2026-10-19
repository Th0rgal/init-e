import InitECandidate.Runtime.HashGetTailValueCell
import InitECandidate.Runtime.HashTableValuesIn
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- The real get tail returns a member of the witness registry whenever present.
The occupied-or-sentinel premise is supplied by actual find-slot execution. -/
theorem hashGetTail_returned_values_in {F : Type} (s post : PanSemStateFiniteExact 64 F)
    (table index capacity used values : BitVec 64) (targets : Set (BitVec 64))
    (tableLocal : s.locals.lookup (ofString "t") = some (.val (.word table)))
    (indexLocal : s.locals.lookup (ofString "i") = some (.val (.word index)))
    (selected : index = capacity ∨ (index.toNat < capacity.toNat ∧ hashOccupancyRead s used index ≠ some 0))
    (domain16 : s.memaddrs (table + 16)) (cell16 : s.memory (table + 16) = .word capacity)
    (domain40 : s.memaddrs (table + 40)) (cell40 : s.memory (table + 40) = .word values)
    (cell48 : s.memory (table + 48) = .word used)
    (valueDomain : ∀ slot : BitVec 64, slot.toNat < capacity.toNat → s.memaddrs (values + slot * 8))
    (entries : HashTableValuesIn table targets s) (v : ValueHOL 64)
    (run : evaluateHOLFiniteState s hashGetTail = (some (.returned v),post)) :
    ∃ present value : BitVec 64, v = .rStruct [.val (.word present),.val (.word value)] ∧
      (present = 0 ∨ present = 1) ∧ (present ≠ 0 → value ∈ targets) := by
  have inside : index.toNat ≤ capacity.toNat := by
    rcases selected with same | ⟨lt,_⟩
    · rw [same]
    · exact Nat.le_of_lt lt
  obtain ⟨present,value,boolean,tail,cell⟩ := evaluate_hashGetTail_value_cell s table index capacity values
    tableLocal indexLocal inside domain16 cell16 domain40 cell40 valueDomain
  have same := (congrArg Prod.fst (run.symm.trans tail))
  have shape : v = .rStruct [.val (.word present),.val (.word value)] := by simpa using same
  refine ⟨present,value,shape,boolean,fun nonzero => ?_⟩
  obtain ⟨lt,valueCell⟩ := cell nonzero
  have occupied : hashOccupancyRead s used index ≠ some 0 := by
    rcases selected with same | ⟨_,occupied⟩
    · rw [same] at lt
      exact False.elim (Nat.lt_irrefl _ lt)
    · exact occupied
  exact entries capacity used values cell16 cell48 cell40 index lt occupied value valueCell

#print axioms hashGetTail_returned_values_in
end InitECandidate.Runtime
