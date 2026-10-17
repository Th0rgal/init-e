import InitECandidate.Runtime.RollbackWorldJournalDeletePresentRoomRegisteredValuesIn
import InitECandidate.Runtime.JournalOverflow32
import InitECandidate.Runtime.TrapCallNoReturn
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- Successful present-key deletion preserves the enlarged saved-value journal; the full-journal trap cannot return. -/
theorem RollbackWorld.journal_delete_present_registered_values_in {F : Type} {widths : BitVec 64 → BitVec 64} {tables : Set (BitVec 64)}
    {journal snapshot count : BitVec 64} {state : PanSemStateFiniteExact 64 F}
    (world : RollbackWorld widths tables journal snapshot count state)
    (separated : RollbackPhysicalSeparated widths tables state)
    (witness : BitVec 64) (member : witness ∈ tables)
    (pointer source size : BitVec 64)
    (keyLocal : state.locals.lookup (ofString "key") = some (.val (.word source)))
    (code : state.code = originalRuntimeCode) (ticks : 2 ^ 42 + size.toNat + 2 ≤ state.clock)
    (heap : state.globals.lookup (ofString "heap_ptr") = some (.val (.word pointer)))
    (pointerBound : pointer.toNat ≤ 33806089496)
    (aligned : pointer.toNat % 8 = 0) (sourceAligned : source.toNat % 8 = 0)
    (sourceWords : ∀ offset : Nat, offset < size.toNat → state.memaddrs (source + BitVec.ofNat 64 offset))
    (sourceBytes : ∀ offset : Nat, offset < size.toNat → state.memaddrs (panByteAlignHOL (source + BitVec.ofNat 64 offset)))
    (present oldValue : BitVec 64)
    (widthEq : size = widths witness)
    (supported : widths witness = 20 ∨ widths witness = 32 ∨ widths witness = 52)
    (tableLocal : state.locals.lookup (ofString "t") = some (.val (.word witness)))
    (oldLocal : state.locals.lookup (ofString "old") = some (.rStruct [.val (.word present),.val (.word oldValue)]))
    (journalBound : journal.toNat + 524288 * 32 ≤ 33806089496)
    (journalAligned : journal.toNat % 8 = 0)
    (journalHeaders : ∀ other ∈ tables, journal.toNat + 524288 * 32 ≤ other.toNat)
    (heapDomain : ∀ address : BitVec 64, address.toNat < 33806089496 → state.memaddrs address)
    (capacityGlobal : state.globals.lookup (ofString "journal_cap") = some (.val (.word (524288 : BitVec 64))))
    (watched targets : Set (BitVec 64)) (watchedSubset : watched ⊆ tables)
    (tableValues : ∀ table ∈ watched, HashTableValuesIn table targets state)
    (savedValues : JournalSavedValuesIn journal count.toNat watched targets state)
    (registered : witness ∈ watched → oldValue ∈ targets)
    (returnedValue : ValueHOL 64)
    (success : (evaluateHOLFiniteState state journalDeletePresent32).1 = some (.returned returnedValue)) :
    JournalSavedValuesIn journal (count + 1).toNat watched targets (evaluateHOLFiniteState state journalDeletePresent32).2 ∧
    (∀ other ∈ watched, HashTableValuesIn other targets (evaluateHOLFiniteState state journalDeletePresent32).2) ∧
    (evaluateHOLFiniteState state journalDeletePresent32).2.globals.lookup (ofString "journal_n") = some (.val (.word (count + 1))) := by
  by_cases space : count.toNat < 524288
  · exact world.journal_delete_present_room_registered_values_in separated witness member pointer source size keyLocal code ticks heap pointerBound aligned sourceAligned
      sourceWords sourceBytes present oldValue widthEq supported tableLocal oldLocal space journalBound journalAligned journalHeaders heapDomain capacityGlobal watched targets watchedSubset tableValues savedValues registered returnedValue success
  · have full : (524288 : BitVec 64).toNat ≤ count.toNat := by change 524288 ≤ count.toNat; omega
    have run : evaluateHOLFiniteState state journalDeletePresent32 =
        evaluateHOLFiniteState state (.call (some (none,none)) (ofString "trap_with") [.const 5]) :=
      evaluate_journal_overflow32 state count 524288 5 _ code world.counter capacityGlobal full
    have args : evalListHOLFinite state (h := fun address => Classical.propDecidable (state.memaddrs address)) [.const 5] = some [.val (.word (5 : BitVec 64))] := by rfl
    have noReturn := evaluate_trap_call_no_return state (.const 5) 5 returnedValue code args
    exact False.elim (noReturn ((congrArg Prod.fst run).symm.trans success))

#print axioms RollbackWorld.journal_delete_present_registered_values_in
end InitECandidate.Runtime
