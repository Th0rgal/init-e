import InitECandidate.Runtime.RollbackWorldJournalDeletePresent
import InitECandidate.Runtime.JournalDeleteAbsent32
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- The original after-get deletion suffix covers absent keys as well as
all journal-guard and saved-key allocation outcomes. -/
theorem RollbackWorld.journal_delete_after_get_bounded {F : Type} {widths : BitVec 64 → BitVec 64} {tables : Set (BitVec 64)}
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
    (capacityGlobal : state.globals.lookup (ofString "journal_cap") = some (.val (.word (524288 : BitVec 64)))) :
    state.clock ≤ (evaluateHOLFiniteState state journalDeleteAfterGet32).2.clock + (2 ^ 42 + size.toNat + 2) ∧
      (evaluateHOLFiniteState state journalDeleteAfterGet32).2.clock ≤ state.clock ∧
      (evaluateHOLFiniteState state journalDeleteAfterGet32).1 ≠ none ∧
      (evaluateHOLFiniteState state journalDeleteAfterGet32).1 ≠ some .timeOut := by
  by_cases absent : present = 0
  · have run := evaluate_journalDelete_absent32 state oldValue (by simpa only [absent] using oldLocal)
    rw [run]
    simp [emptyLocalsHOLFinite]
  · have condition : @evalHOLExact 64 F _ state.toExact (fun address => Classical.propDecidable (state.memaddrs address))
        (.cmp .equal (.rfield 0 (.var .local (ofString "old"))) (.const 0)) = some (.val (.word (0 : BitVec 64))) := by
      simp [evalHOLExact,oldLocal,Compiler.Encoders.Asm.wordCmpHOL]
      exact absent
    have guard : evaluateHOLFiniteState state
        (.ite (.cmp .equal (.rfield 0 (.var .local (ofString "old"))) (.const 0)) (.return (.const 0)) .skip) = (none,state) := by
      rw [evaluateHOLFiniteState_ite,condition]
      simp [evaluateHOLFiniteState_skip]
    have bounded := world.journal_delete_present_bounded separated witness member pointer source size keyLocal code ticks heap pointerBound aligned sourceAligned
      sourceWords sourceBytes present oldValue widthEq supported tableLocal oldLocal journalBound journalAligned journalHeaders heapDomain capacityGlobal
    unfold journalDeleteAfterGet32
    rw [evaluateHOLFiniteState_seq_line780,guard]
    exact bounded

#print axioms RollbackWorld.journal_delete_after_get_bounded
end InitECandidate.Runtime
