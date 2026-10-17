import InitECandidate.Runtime.RollbackWorldJournalDeleteAllocateCopyFields
import InitECandidate.Runtime.AllocationCopyDomains
import InitECandidate.Runtime.AllocationBodyBound
import InitECandidate.Runtime.AllocationFailureDeclarationNoReturn
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- Successful returns preserve the enlarged world for every saved-key request;
rejected requests are excluded by the allocator's checked no-return property. -/
theorem RollbackWorld.journal_delete_allocate_copy_fields_all_requests {F : Type} {widths : BitVec 64 → BitVec 64} {tables : Set (BitVec 64)}
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
    (aligned : pointer.toNat % 8 = 0) (sourceAligned : source.toNat % 8 = 0)
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
    (heapDomain : ∀ address : BitVec 64, address.toNat < 33806089496 → state.memaddrs address)
    (ts fieldPointer : BitVec 64)
    (tsFields : StateFreshTxFields ts fieldPointer stateFreshTxAllTables state)
    (tsBound : ts.toNat + 72 ≤ 33806089496)
    (journalBeforeTs : journal.toNat + 524288 * 32 ≤ ts.toNat)
    (headerBefore : ts.toNat + 72 ≤ witness.toNat)
    (returnedValue : ValueHOL 64)
    (success : (evaluateHOLFiniteState state journalDeleteAllocateCopy32).1 = some (.returned returnedValue)) :
    RollbackWorld widths tables journal snapshot (count + 1)
      (setVarHOLFinite (ofString "snap") (.val (.word snapshot)) (evaluateHOLFiniteState state journalDeleteAllocateCopy32).2) ∧
      RollbackPhysicalSeparated widths tables (evaluateHOLFiniteState state journalDeleteAllocateCopy32).2 ∧
      StateFreshTxFields ts fieldPointer stateFreshTxAllTables (evaluateHOLFiniteState state journalDeleteAllocateCopy32).2 := by
  by_cases request : size ≤ (33806089496 : BitVec 64) - pointer
  · have finish := allocationEnd_within_heap pointer size pointerBound request
    obtain ⟨wordDomain,byteDomain⟩ := allocation_copy_domains state pointer size pointerBound request heapDomain
    exact world.journal_delete_allocate_copy_fields separated witness member pointer source size keyLocal sizeLocal code ticks heap pointerBound request finish
      aligned sourceAligned wordDomain byteDomain sourceWords sourceBytes present oldValue widthEq supported tableLocal oldLocal
      space journalBound journalAligned journalHeaders heapDomain ts fieldPointer tsFields tsBound journalBeforeTs headerBefore
  · have rejected : ((33806089496 : BitVec 64) - pointer).toNat < size.toNat := by
      have notLe : ¬ size.toNat ≤ ((33806089496 : BitVec 64) - pointer).toNat := fun le => request (BitVec.le_def.mpr le)
      omega
    have args : evalListHOLFinite state (h := fun address => Classical.propDecidable (state.memaddrs address)) [.var .local (ofString "klen")] = some [.val (.word size)] := by
      simp [evalListHOLFinite,evalListHOLExact,evalHOLExact,sizeLocal]
    have noReturn := evaluate_alloc_request_failure_declaration_no_return state (.var .local (ofString "klen")) pointer size (ofString "kc") .one journalDeleteCopy32 returnedValue args code heap rejected
    exact False.elim (noReturn success)

#print axioms RollbackWorld.journal_delete_allocate_copy_fields_all_requests
end InitECandidate.Runtime
