import InitECandidate.Runtime.RollbackWorldJournalSetAfterGetRoom
import InitECandidate.Runtime.JournalOverflow32
import InitECandidate.Runtime.TrapCallNoTimeout
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- The complete original after-get suffix is bounded regardless of journal
capacity guard outcome and saved-key allocator success or failure. -/
theorem RollbackWorld.journal_set_after_get_bounded {F : Type} {widths : BitVec 64 → BitVec 64} {tables : Set (BitVec 64)}
    {journal snapshot count : BitVec 64} {state : PanSemStateFiniteExact 64 F}
    (world : RollbackWorld widths tables journal snapshot count state)
    (separated : RollbackPhysicalSeparated widths tables state)
    (witness : BitVec 64) (member : witness ∈ tables)
    (pointer source size : BitVec 64)
    (keyLocal : state.locals.lookup (ofString "key") = some (.val (.word source)))
    (code : state.code = originalRuntimeCode) (ticks : 2 ^ 72 + size.toNat + 2 ≤ state.clock)
    (heap : state.globals.lookup (ofString "heap_ptr") = some (.val (.word pointer)))
    (pointerBound : pointer.toNat ≤ 33806089496)
    (aligned : pointer.toNat % 8 = 0) (sourceAligned : source.toNat % 8 = 0)
    (sourceWords : ∀ offset : Nat, offset < size.toNat → state.memaddrs (source + BitVec.ofNat 64 offset))
    (sourceBytes : ∀ offset : Nat, offset < size.toNat → state.memaddrs (panByteAlignHOL (source + BitVec.ofNat 64 offset)))
    (present oldValue newValue : BitVec 64)
    (widthEq : size = widths witness)
    (supported : widths witness = 20 ∨ widths witness = 32 ∨ widths witness = 52)
    (tableLocal : state.locals.lookup (ofString "t") = some (.val (.word witness)))
    (oldLocal : state.locals.lookup (ofString "old") = some (.rStruct [.val (.word present),.val (.word oldValue)]))
    (valueLocal : state.locals.lookup (ofString "value") = some (.val (.word newValue)))
    (journalBound : journal.toNat + 524288 * 32 ≤ 33806089496)
    (journalAligned : journal.toNat % 8 = 0)
    (journalHeaders : ∀ other ∈ tables, journal.toNat + 524288 * 32 ≤ other.toNat)
    (heapDomain : ∀ address : BitVec 64, address.toNat < 33806089496 → state.memaddrs address)
    (capacityGlobal : state.globals.lookup (ofString "journal_cap") = some (.val (.word (524288 : BitVec 64)))) :
    state.clock ≤ (evaluateHOLFiniteState state journalSetAfterGet32).2.clock + (2 ^ 72 + size.toNat + 2) ∧
      (evaluateHOLFiniteState state journalSetAfterGet32).2.clock ≤ state.clock ∧
      (evaluateHOLFiniteState state journalSetAfterGet32).1 ≠ none ∧
      (evaluateHOLFiniteState state journalSetAfterGet32).1 ≠ some .timeOut := by
  by_cases space : count.toNat < 524288
  · exact world.journal_set_after_get_room_bounded separated witness member pointer source size keyLocal code ticks heap pointerBound aligned sourceAligned
      sourceWords sourceBytes present oldValue newValue widthEq supported tableLocal oldLocal valueLocal space journalBound journalAligned journalHeaders heapDomain capacityGlobal
  · have full : (524288 : BitVec 64).toNat ≤ count.toNat := by change 524288 ≤ count.toNat; omega
    have stopped := evaluate_journal_set_overflow32 state count 524288 code world.counter capacityGlobal full
    have run : evaluateHOLFiniteState state journalSetAfterGet32 =
        evaluateHOLFiniteState state (.call (some (none,none)) (ofString "trap_with") [.const 4]) :=
      evaluate_journal_overflow32 state count 524288 4 _ code world.counter capacityGlobal full
    have args : evalListHOLFinite state (h := fun address => Classical.propDecidable (state.memaddrs address)) [.const 4] = some [.val (.word (4 : BitVec 64))] := by rfl
    have noTimeout := evaluate_trap_call_no_timeout state (.const 4) 4 (by omega) code args
    refine ⟨by rw [stopped.2]; omega,by rw [stopped.2]; omega,stopped.1,?_⟩
    rw [run]
    exact noTimeout

#print axioms RollbackWorld.journal_set_after_get_bounded
end InitECandidate.Runtime
