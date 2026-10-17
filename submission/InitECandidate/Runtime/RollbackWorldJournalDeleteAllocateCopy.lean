import InitECandidate.Runtime.RollbackWorldAllocateCopyKey
import InitECandidate.Runtime.RollbackWorldJournalDeleteScope
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- Original deletion allocation and copy/record/delete continuation. -/
def journalDeleteAllocateCopy32 : ProgHOL 64 :=
  .decCall (ofString "kc") .one (ofString "alloc") [.var .local (ofString "klen")] journalDeleteCopy32

theorem journalDeletePresent32_allocate_copy : journalDeletePresent32 =
    .seq (.ite (.cmp .notLower (.var .global (ofString "journal_n")) (.var .global (ofString "journal_cap")))
      (.call (some (none,none)) (ofString "trap_with") [.const 5]) .skip)
      (.dec (ofString "klen") .one (.load .one (.op .add [.var .local (ofString "t"),.const 0])) journalDeleteAllocateCopy32) := by rfl

/-- Successful saved-key allocation followed by the full original journal
deletion path has a uniform clock bound and returns without timeout. -/
theorem RollbackWorld.journal_delete_allocate_copy_bounded {F : Type} {widths : BitVec 64 → BitVec 64} {tables : Set (BitVec 64)}
    {journal snapshot count : BitVec 64} {state : PanSemStateFiniteExact 64 F}
    (world : RollbackWorld widths tables journal snapshot count state)
    (separated : RollbackPhysicalSeparated widths tables state)
    (witness : BitVec 64) (member : witness ∈ tables)
    (pointer source size : BitVec 64)
    (keyLocal : state.locals.lookup (ofString "key") = some (.val (.word source)))
    (sizeLocal : state.locals.lookup (ofString "klen") = some (.val (.word size)))
    (code : state.code = originalRuntimeCode) (ticks : 2 ^ 42 + size.toNat + 2 ≤ state.clock)
    (heap : state.globals.lookup (ofString "heap_ptr") = some (.val (.word pointer)))
    (pointerBound : pointer.toNat ≤ 33806089496)
    (request : size ≤ (33806089496 : BitVec 64) - pointer)
    (finish : (allocationEnd pointer size).toNat ≤ 33806089496)
    (aligned : pointer.toNat % 8 = 0) (sourceAligned : source.toNat % 8 = 0)
    (wordDomain : ∀ offset : Nat, offset < size.toNat → state.memaddrs (pointer + BitVec.ofNat 64 offset))
    (byteDomain : ∀ offset : Nat, offset < size.toNat → state.memaddrs (panByteAlignHOL (pointer + BitVec.ofNat 64 offset)))
    (sourceWords : ∀ offset : Nat, offset < size.toNat → state.memaddrs (source + BitVec.ofNat 64 offset))
    (sourceBytes : ∀ offset : Nat, offset < size.toNat → state.memaddrs (panByteAlignHOL (source + BitVec.ofNat 64 offset)))
    (present oldValue : BitVec 64)
    (widthEq : size = widths witness)
    (supported : widths witness = 20 ∨ widths witness = 32 ∨ widths witness = 52)
    (tableLocal : state.locals.lookup (ofString "t") = some (.val (.word witness)))
    (oldLocal : state.locals.lookup (ofString "old") = some (.rStruct [.val (.word present),.val (.word oldValue)]))
    (space : count.toNat < 524288)
    (journalBound : journal.toNat + 524288 * 32 ≤ 33806089496)
    (journalAligned : journal.toNat % 8 = 0)
    (journalHeaders : ∀ other ∈ tables, journal.toNat + 524288 * 32 ≤ other.toNat)
    (heapDomain : ∀ address : BitVec 64, address.toNat < 33806089496 → state.memaddrs address) :
    state.clock ≤ (evaluateHOLFiniteState state journalDeleteAllocateCopy32).2.clock + (2 ^ 42 + size.toNat + 2) ∧
      (evaluateHOLFiniteState state journalDeleteAllocateCopy32).2.clock ≤ state.clock ∧
      (evaluateHOLFiniteState state journalDeleteAllocateCopy32).1 = some (.returned (.val (.word (0 : BitVec 64)))) := by
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
  obtain ⟨post,suffixRun,_,_,suffixCost,suffixRemaining⟩ := midWorld.journal_delete_record_scope_bounded midSep witness pointer present oldValue member space journalBound journalAligned journalHeaders
    (by intro address upper; rw [domain]; exact heapDomain address upper) supported aligned
    (by simpa only [domain,← widthEq] using wordDomain) (by simpa only [domain,← widthEq] using byteDomain)
    atT atKc atOld source atKey sourceAligned
    (by simpa only [domain,← widthEq] using sourceWords) (by simpa only [domain,← widthEq] using sourceBytes) (by omega)
  have fullRun : evaluateHOLFiniteState state journalDeleteAllocateCopy32 =
      (let output := evaluateHOLFiniteState middle journalDeleteRecordScope32;
        (output.1,{output.2 with locals := HolFiniteMapExact.resVarEq output.2.locals (ofString "kc",state.locals.lookup (ofString "kc"))})) :=
    run journalDeleteRecordScope32
  rw [fullRun,suffixRun]
  exact ⟨by dsimp only [emptyLocalsHOLFinite]; omega,by dsimp only [emptyLocalsHOLFinite]; omega,rfl⟩

#print axioms journalDeletePresent32_allocate_copy
#print axioms RollbackWorld.journal_delete_allocate_copy_bounded
end InitECandidate.Runtime
