import InitECandidate.Runtime.RollbackWorldJournalDeletePresentSuccess
import InitECandidate.Runtime.JournalDeleteAbsent32
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- Successful deletion appends one record exactly on the present-key path;
the absent-key early return retains the old count and complete world. -/
theorem RollbackWorld.journal_delete_after_get_success {F : Type} {widths : BitVec 64 → BitVec 64} {tables : Set (BitVec 64)}
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
    (returnedValue : ValueHOL 64)
    (success : (evaluateHOLFiniteState state journalDeleteAfterGet32).1 = some (.returned returnedValue)) :
    ∃ next : BitVec 64, (next = count ∨ next = count + 1) ∧
      RollbackWorld widths tables journal snapshot next
        (setVarHOLFinite (ofString "snap") (.val (.word snapshot)) (evaluateHOLFiniteState state journalDeleteAfterGet32).2) ∧
      RollbackPhysicalSeparated widths tables (evaluateHOLFiniteState state journalDeleteAfterGet32).2 := by
  by_cases absent : present = 0
  · have run := evaluate_journalDelete_absent32 state oldValue (by simpa only [absent] using oldLocal)
    refine ⟨count,Or.inl rfl,?_,?_⟩
    · rw [run]
      exact world.after_logical_frame rfl rfl rfl rfl rfl
    · rw [run]
      exact separated.after_read rfl rfl rfl rfl rfl
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
    obtain ⟨valid,apart⟩ := world.journal_delete_present_success separated witness member pointer source size keyLocal code ticks heap pointerBound aligned sourceAligned
      sourceWords sourceBytes present oldValue widthEq supported tableLocal oldLocal journalBound journalAligned journalHeaders heapDomain capacityGlobal returnedValue presentSuccess
    refine ⟨count + 1,Or.inr rfl,?_,?_⟩
    · rw [run]; exact valid
    · rw [run]; exact apart

#print axioms RollbackWorld.journal_delete_after_get_success
end InitECandidate.Runtime
