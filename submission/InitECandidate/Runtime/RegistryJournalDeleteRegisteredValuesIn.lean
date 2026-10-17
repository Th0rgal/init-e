import InitECandidate.Runtime.TransactionRegistryWorld
import InitECandidate.Runtime.RollbackWorldJournalDeleteCallRegisteredValuesIn
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- Actual jdel retains the full transaction world, watched table values, and
saved journal values on successful return, including all allocation plans. -/
theorem TransactionRegistryWorld.jdel_call_registered_values_in {F : Type} (state : PanSemStateFiniteExact 64 F)
    (widths : BitVec 64 → BitVec 64) (tables : Set (BitVec 64)) (fieldPointer ts journal snapshot count table key : BitVec 64)
    (valid : TransactionRegistryWorld widths tables fieldPointer ts journal snapshot count state)
    (member : table ∈ tables)
    (tableArgument keyArgument : ExpHOL 64)
    (arguments : evalListHOLFinite state (h := fun address => Classical.propDecidable (state.memaddrs address))
      [tableArgument,keyArgument] = some [.val (.word table),.val (.word key)])
    (keyAligned : key.toNat % 8 = 0)
    (keyWords : ∀ offset : Nat, offset < (widths table).toNat → state.memaddrs (key + BitVec.ofNat 64 offset))
    (keyBytes : ∀ offset : Nat, offset < (widths table).toNat → state.memaddrs (panByteAlignHOL (key + BitVec.ofNat 64 offset)))
    (ticks : 2 ^ 43 + 1 ≤ state.clock)
    (watched targets : Set (BitVec 64)) (watchedSubset : watched ⊆ tables)
    (registered : ∀ other ∈ watched, HashTableValuesIn other targets state)
    (saved : JournalSavedValuesIn journal count.toNat watched targets state)
    :
    let output := evaluateHOLFiniteState state (.call (some (none,none)) (ofString "jdel") [tableArgument,keyArgument]);
    output.1 ≠ some .timeOut ∧ state.clock ≤ output.2.clock + (2 ^ 43 + 1) ∧ output.2.clock ≤ state.clock ∧
      (output.1 = none → ∃ next : BitVec 64, (next = count ∨ next = count + 1) ∧ TransactionRegistryWorld widths tables fieldPointer ts journal snapshot next output.2 ∧
        (∀ other ∈ watched, HashTableValuesIn other targets output.2) ∧ JournalSavedValuesIn journal next.toNat watched targets output.2) := by
  have contract := valid.jdel_call state widths tables fieldPointer ts journal snapshot count table key member
    tableArgument keyArgument arguments keyAligned keyWords keyBytes (by omega)
  refine ⟨contract.1,(by have := contract.2.1; omega),contract.2.2.1,?_⟩
  intro success
  have membership := rollback_world_jdel_call_registered_values_in state widths tables journal snapshot count table key
    valid.journalWorld.world valid.journalWorld.separated member (valid.journalWorld.supported table member)
    tableArgument keyArgument arguments keyAligned keyWords keyBytes ticks
    valid.journalWorld.journalBound valid.journalWorld.journalAligned valid.journalWorld.journalHeaders
    valid.journalWorld.heapDomain valid.journalWorld.capacity valid.journalWorld.code
    watched targets watchedSubset registered saved success
  obtain ⟨next,counts,postWorld⟩ := contract.2.2.2 success
  obtain ⟨savedCount,_,postSaved,postValues,postCounter⟩ := membership
  have sameCount : savedCount = next := by
    have equal := postCounter.symm.trans postWorld.journalWorld.world.counter
    simpa only [Option.some.injEq,ValueHOL.val.injEq,HolWordLab.word.injEq] using equal
  subst savedCount
  exact ⟨next,counts,postWorld,postValues,postSaved⟩

#print axioms TransactionRegistryWorld.jdel_call_registered_values_in
end InitECandidate.Runtime
