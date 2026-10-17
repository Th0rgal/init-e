import InitECandidate.Runtime.RollbackWorldAllocateCopyKey
import InitECandidate.Runtime.RollbackWorldJournalSetScope
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- Original allocation and copy/record/set continuation after reading klen. -/
def journalSetAllocateCopy32 : ProgHOL 64 :=
  .decCall (ofString "kc") .one (ofString "alloc") [.var .local (ofString "klen")] journalSetCopy32

/-- Exact placement in the original guarded, key-width-reading suffix. -/
theorem journalSetAfterGet32_allocate_copy : journalSetAfterGet32 =
    .seq (.ite (.cmp .notLower (.var .global (ofString "journal_n")) (.var .global (ofString "journal_cap")))
      (.call (some (none,none)) (ofString "trap_with") [.const 4]) .skip)
      (.dec (ofString "klen") .one (.load .one (.op .add [.var .local (ofString "t"),.const 0])) journalSetAllocateCopy32) := by rfl

/-- On a successful saved-key allocation, the entire remaining journal-set
path has a uniform clock bound and cannot time out, for all table-growth plans. -/
theorem RollbackWorld.journal_set_allocate_copy_bounded {F : Type} {widths : BitVec 64 → BitVec 64} {tables : Set (BitVec 64)}
    {journal snapshot count : BitVec 64} {state : PanSemStateFiniteExact 64 F}
    (world : RollbackWorld widths tables journal snapshot count state)
    (separated : RollbackPhysicalSeparated widths tables state)
    (witness : BitVec 64) (member : witness ∈ tables)
    (pointer source size : BitVec 64)
    (keyLocal : state.locals.lookup (ofString "key") = some (.val (.word source)))
    (sizeLocal : state.locals.lookup (ofString "klen") = some (.val (.word size)))
    (code : state.code = originalRuntimeCode) (ticks : 2 ^ 72 + size.toNat + 2 ≤ state.clock)
    (heap : state.globals.lookup (ofString "heap_ptr") = some (.val (.word pointer)))
    (pointerBound : pointer.toNat ≤ 33806089496)
    (request : size ≤ (33806089496 : BitVec 64) - pointer)
    (finish : (allocationEnd pointer size).toNat ≤ 33806089496)
    (aligned : pointer.toNat % 8 = 0) (sourceAligned : source.toNat % 8 = 0)
    (wordDomain : ∀ offset : Nat, offset < size.toNat → state.memaddrs (pointer + BitVec.ofNat 64 offset))
    (byteDomain : ∀ offset : Nat, offset < size.toNat → state.memaddrs (panByteAlignHOL (pointer + BitVec.ofNat 64 offset)))
    (sourceWords : ∀ offset : Nat, offset < size.toNat → state.memaddrs (source + BitVec.ofNat 64 offset))
    (sourceBytes : ∀ offset : Nat, offset < size.toNat → state.memaddrs (panByteAlignHOL (source + BitVec.ofNat 64 offset)))
    (present oldValue newValue : BitVec 64)
    (widthEq : size = widths witness)
    (supported : widths witness = 20 ∨ widths witness = 32 ∨ widths witness = 52)
    (tableLocal : state.locals.lookup (ofString "t") = some (.val (.word witness)))
    (oldLocal : state.locals.lookup (ofString "old") = some (.rStruct [.val (.word present),.val (.word oldValue)]))
    (valueLocal : state.locals.lookup (ofString "value") = some (.val (.word newValue)))
    (space : count.toNat < 524288)
    (journalBound : journal.toNat + 524288 * 32 ≤ 33806089496)
    (journalAligned : journal.toNat % 8 = 0)
    (journalHeaders : ∀ other ∈ tables, journal.toNat + 524288 * 32 ≤ other.toNat)
    (heapDomain : ∀ address : BitVec 64, address.toNat < 33806089496 → state.memaddrs address) :
    state.clock ≤ (evaluateHOLFiniteState state journalSetAllocateCopy32).2.clock + (2 ^ 72 + size.toNat + 2) ∧
      (evaluateHOLFiniteState state journalSetAllocateCopy32).2.clock ≤ state.clock ∧
      (evaluateHOLFiniteState state journalSetAllocateCopy32).1 ≠ none ∧
      (evaluateHOLFiniteState state journalSetAllocateCopy32).1 ≠ some .timeOut ∧
      (evaluateHOLFiniteState state journalSetAllocateCopy32).1 ≠ some .continue := by
  obtain ⟨middle,run,midWorld,midSep,cost,remaining,locals,domain,midCode,_,_,_⟩ :=
    world.allocate_copy_key separated witness member pointer source size keyLocal sizeLocal code (by omega) heap pointerBound request finish aligned sourceAligned
      wordDomain byteDomain sourceWords sourceBytes
  have atKc : middle.locals.lookup (ofString "kc") = some (.val (.word pointer)) := by
    rw [locals]; simp [setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]
  have atT : middle.locals.lookup (ofString "t") = some (.val (.word witness)) := by
    rw [locals]; simpa [setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,show ofString "kc" ≠ ofString "t" from by decide] using tableLocal
  have atOld : middle.locals.lookup (ofString "old") = some (.rStruct [.val (.word present),.val (.word oldValue)]) := by
    rw [locals]; simpa [setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,show ofString "kc" ≠ ofString "old" from by decide] using oldLocal
  have atKey : middle.locals.lookup (ofString "key") = some (.val (.word source)) := by
    rw [locals]; simpa [setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,show ofString "kc" ≠ ofString "key" from by decide] using keyLocal
  have atValue : middle.locals.lookup (ofString "value") = some (.val (.word newValue)) := by
    rw [locals]; simpa [setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,show ofString "kc" ≠ ofString "value" from by decide] using valueLocal
  obtain ⟨bounded,outcome⟩ := midWorld.journal_set_record_scope_bounded midSep witness pointer present oldValue member space journalBound journalAligned journalHeaders
    (by intro address upper; rw [domain]; exact heapDomain address upper) supported aligned
    (by simpa only [domain,← widthEq] using wordDomain) (by simpa only [domain,← widthEq] using byteDomain)
    atT atKc atOld source newValue atKey atValue sourceAligned
    (by simpa only [domain,← widthEq] using sourceWords) (by simpa only [domain,← widthEq] using sourceBytes) (by omega)
  have fullRun : evaluateHOLFiniteState state journalSetAllocateCopy32 =
      (let output := evaluateHOLFiniteState middle journalSetRecordScope32;
        (output.1,{output.2 with locals := HolFiniteMapExact.resVarEq output.2.locals (ofString "kc",state.locals.lookup (ofString "kc"))})) := by
    exact run journalSetRecordScope32
  have terminal : (evaluateHOLFiniteState middle journalSetRecordScope32).1 ≠ none ∧
      (evaluateHOLFiniteState middle journalSetRecordScope32).1 ≠ some .timeOut ∧
      (evaluateHOLFiniteState middle journalSetRecordScope32).1 ≠ some .continue := by
    rcases outcome with success | failure
    · obtain ⟨post,successRun,_,_⟩ := success
      rw [successRun]
      simp
    · exact ⟨failure.1,failure.2.1,failure.2.2.2⟩
  rw [fullRun]
  exact ⟨by dsimp only; omega,by dsimp only; omega,terminal.1,terminal.2.1,terminal.2.2⟩

#print axioms journalSetAfterGet32_allocate_copy
#print axioms RollbackWorld.journal_set_allocate_copy_bounded
end InitECandidate.Runtime
