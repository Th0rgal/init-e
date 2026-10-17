import InitECandidate.Runtime.RollbackWorldJournalDeletePresentFields
import InitECandidate.Runtime.JournalDeleteAbsent32
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- Successful original journal-delete execution preserves all eight transaction
table fields through this scope, without adding source locals or parameters. -/
theorem RollbackWorld.journal_delete_after_get_success_fields {F : Type} {widths : BitVec 64 → BitVec 64} {tables : Set (BitVec 64)}
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
    (ts fieldPointer : BitVec 64)
    (tsFields : StateFreshTxFields ts fieldPointer stateFreshTxAllTables state)
    (tsBound : ts.toNat + 72 ≤ 33806089496)
    (journalBeforeTs : journal.toNat + 524288 * 32 ≤ ts.toNat)
    (headerBefore : ts.toNat + 72 ≤ witness.toNat)
    (returnedValue : ValueHOL 64)
    (success : (evaluateHOLFiniteState state journalDeleteAfterGet32).1 = some (.returned returnedValue)) :
    StateFreshTxFields ts fieldPointer stateFreshTxAllTables
      (evaluateHOLFiniteState state journalDeleteAfterGet32).2 := by
  by_cases absent : present = 0
  · have run := evaluate_journalDelete_absent32 state oldValue (by simpa only [absent] using oldLocal)
    rw [run]
    exact tsFields.after_memory rfl
  · have condition : @evalHOLExact 64 F _ state.toExact (fun address => Classical.propDecidable (state.memaddrs address))
        (.cmp .equal (.rfield 0 (.var .local (ofString "old"))) (.const 0)) = some (.val (.word (0 : BitVec 64))) := by
      simp [evalHOLExact,oldLocal,Compiler.Encoders.Asm.wordCmpHOL]
      exact absent
    have guard : evaluateHOLFiniteState state
        (.ite (.cmp .equal (.rfield 0 (.var .local (ofString "old"))) (.const 0)) (.return (.const 0)) .skip) = (none,state) := by
      rw [evaluateHOLFiniteState_ite,condition]
      simp [evaluateHOLFiniteState_skip]
    have run : evaluateHOLFiniteState state journalDeleteAfterGet32 = evaluateHOLFiniteState state journalDeletePresent32 :=
      evaluate_seq_none guard rfl
    have presentSuccess : (evaluateHOLFiniteState state journalDeletePresent32).1 = some (.returned returnedValue) :=
      (congrArg Prod.fst run).symm.trans success
    have frame := world.journal_delete_present_success_fields separated witness member pointer source size keyLocal code ticks heap pointerBound aligned sourceAligned
      sourceWords sourceBytes present oldValue widthEq supported tableLocal oldLocal journalBound journalAligned journalHeaders heapDomain capacityGlobal ts fieldPointer tsFields tsBound journalBeforeTs headerBefore returnedValue presentSuccess
    rw [run]
    exact frame

#print axioms RollbackWorld.journal_delete_after_get_success_fields
end InitECandidate.Runtime
