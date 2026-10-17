import InitECandidate.Runtime.RollbackWorldJournalSetAllocateCopy
import InitECandidate.Runtime.RollbackWorldAllocateCopyKeyValuesIn
import InitECandidate.Runtime.RollbackWorldJournalSetScopeValuesIn
import InitECandidate.Runtime.RollbackWorldLogicalFrame
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- A successful return from the original allocation/copy/journal/set block
preserves the enlarged world in its actual exit state, with snapshot logical. -/
theorem RollbackWorld.journal_set_allocate_copy_values_in {F : Type} {widths : BitVec 64 → BitVec 64} {tables : Set (BitVec 64)}
    {journal snapshot count : BitVec 64} {state : PanSemStateFiniteExact 64 F}
    (world : RollbackWorld widths tables journal snapshot count state)
    (separated : RollbackPhysicalSeparated widths tables state)
    (witness : BitVec 64) (member : witness ∈ tables)
    (pointer source size : BitVec 64)
    (keyLocal : state.locals.lookup (ofString "key") = some (.val (.word source)))
    (sizeLocal : state.locals.lookup (ofString "klen") = some (.val (.word size)))
    (code : state.code = originalRuntimeCode) (ticks : 2 ^ 74 + size.toNat + 2 ≤ state.clock)
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
    (heapDomain : ∀ address : BitVec 64, address.toNat < 33806089496 → state.memaddrs address)
    (targets : Set (BitVec 64)) (registered : HashTableValuesIn witness targets state) (newMember : newValue ∈ targets)
    (returnedValue : ValueHOL 64)
    (success : (evaluateHOLFiniteState state journalSetAllocateCopy32).1 = some (.returned returnedValue)) :
    HashTableValuesIn witness targets (evaluateHOLFiniteState state journalSetAllocateCopy32).2 := by
  obtain ⟨middle,run,midWorld,midSep,midRegistered,cost,remaining,locals,domain,midCode,_,_,_⟩ :=
    world.allocate_copy_key_values_in separated targets (fun table => table = witness)
      (by intro table same; change table = witness at same; subst table; exact member)
      (by intro table same; change table = witness at same; subst table; exact registered) witness member pointer source size keyLocal sizeLocal code (by omega) heap pointerBound request finish aligned sourceAligned
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
  obtain ⟨_,_,_,preserves⟩ := midWorld.journal_set_record_scope_values_in witness pointer present oldValue member space journalBound journalAligned journalHeaders
    (by intro address upper; rw [domain]; exact heapDomain address upper) supported
    atT atKc atOld source newValue atKey atValue sourceAligned
    (by simpa only [domain,← widthEq] using sourceWords) (by simpa only [domain,← widthEq] using sourceBytes)
    targets (midRegistered witness rfl) newMember (by omega)
  have fullRun : evaluateHOLFiniteState state journalSetAllocateCopy32 =
      (let output := evaluateHOLFiniteState middle journalSetRecordScope32;
        (output.1,{output.2 with locals := HolFiniteMapExact.resVarEq output.2.locals (ofString "kc",state.locals.lookup (ofString "kc"))})) := by
    exact run journalSetRecordScope32
  have returned : (evaluateHOLFiniteState middle journalSetRecordScope32).1 = some (.returned returnedValue) := by
    simpa only [fullRun] using success
  have valid := preserves returnedValue returned
  rw [fullRun]
  exact valid.after_read rfl rfl rfl

#print axioms RollbackWorld.journal_set_allocate_copy_values_in
end InitECandidate.Runtime
