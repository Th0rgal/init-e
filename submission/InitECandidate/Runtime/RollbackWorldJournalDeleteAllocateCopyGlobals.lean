import InitECandidate.Runtime.RollbackWorldJournalDeleteAllocateCopy
import InitECandidate.Runtime.RollbackWorldJournalDeleteScopeFrame
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- The saved-key allocation/copy/deletion path preserves all globals except
heap_ptr and journal_n, including the fixed journal capacity. -/
theorem RollbackWorld.journal_delete_allocate_copy_globals {F : Type} {widths : BitVec 64 → BitVec 64} {tables : Set (BitVec 64)}
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
    ∀ name, name ≠ ofString "heap_ptr" → name ≠ ofString "journal_n" →
      (evaluateHOLFiniteState state journalDeleteAllocateCopy32).2.globals.lookup name = state.globals.lookup name := by
  obtain ⟨middle,run,midWorld,midSep,cost,remaining,locals,domain,midCode,_,midGlobals,_⟩ :=
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
  obtain ⟨post,suffixRun,_,_,suffixCost,suffixRemaining,suffixGlobals⟩ := midWorld.journal_delete_record_scope_bounded_frame midSep witness pointer present oldValue member space journalBound journalAligned journalHeaders
    (by intro address upper; rw [domain]; exact heapDomain address upper) supported aligned
    (by simpa only [domain,← widthEq] using wordDomain) (by simpa only [domain,← widthEq] using byteDomain)
    atT atKc atOld source atKey sourceAligned
    (by simpa only [domain,← widthEq] using sourceWords) (by simpa only [domain,← widthEq] using sourceBytes) (by omega)
  have fullRun : evaluateHOLFiniteState state journalDeleteAllocateCopy32 =
      (let output := evaluateHOLFiniteState middle journalDeleteRecordScope32;
        (output.1,{output.2 with locals := HolFiniteMapExact.resVarEq output.2.locals (ofString "kc",state.locals.lookup (ofString "kc"))})) :=
    run journalDeleteRecordScope32
  rw [fullRun,suffixRun]
  intro name notHeap notCounter
  exact (suffixGlobals name notHeap notCounter).trans (midGlobals name notHeap)

#print axioms RollbackWorld.journal_delete_allocate_copy_globals
end InitECandidate.Runtime
