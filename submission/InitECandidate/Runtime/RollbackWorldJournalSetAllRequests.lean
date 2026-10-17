import InitECandidate.Runtime.RollbackWorldJournalSetAllocateCopy
import InitECandidate.Runtime.AllocationCopyDomains
import InitECandidate.Runtime.AllocationBodyBound
import InitECandidate.Runtime.AllocationFailureDeclarationNoTimeout
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- The original saved-key allocation continuation is bounded for every request;
failed requests trap before copying, while successful requests derive all
copy destination domains from the full heap domain. -/
theorem RollbackWorld.journal_set_allocate_copy_all_requests {F : Type} {widths : BitVec 64 → BitVec 64} {tables : Set (BitVec 64)}
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
    (aligned : pointer.toNat % 8 = 0) (sourceAligned : source.toNat % 8 = 0)
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
      (evaluateHOLFiniteState state journalSetAllocateCopy32).1 ≠ some .timeOut := by
  by_cases request : size ≤ (33806089496 : BitVec 64) - pointer
  · have finish := allocationEnd_within_heap pointer size pointerBound request
    obtain ⟨wordDomain,byteDomain⟩ := allocation_copy_domains state pointer size pointerBound request heapDomain
    have bounded := world.journal_set_allocate_copy_bounded separated witness member pointer source size keyLocal sizeLocal code ticks heap pointerBound request finish
      aligned sourceAligned wordDomain byteDomain sourceWords sourceBytes present oldValue newValue widthEq supported tableLocal oldLocal valueLocal
      space journalBound journalAligned journalHeaders heapDomain
    exact ⟨bounded.1,bounded.2.1,bounded.2.2.1,bounded.2.2.2.1⟩
  · have rejected : ((33806089496 : BitVec 64) - pointer).toNat < size.toNat := by
      have notLe : ¬ size.toNat ≤ ((33806089496 : BitVec 64) - pointer).toNat := fun le => request (BitVec.le_def.mpr le)
      omega
    have args : evalListHOLFinite state (h := fun address => Classical.propDecidable (state.memaddrs address)) [.var .local (ofString "klen")] = some [.val (.word size)] := by
      simp [evalListHOLFinite,evalListHOLExact,evalHOLExact,sizeLocal]
    have failed := evaluate_alloc_request_failure_declaration state (.var .local (ofString "klen")) pointer size (ofString "kc") .one journalSetCopy32 args code heap rejected
    have noTimeout := evaluate_alloc_request_failure_declaration_no_timeout state (.var .local (ofString "klen")) pointer size (ofString "kc") .one journalSetCopy32 args code heap rejected (by omega)
    change (evaluateHOLFiniteState state journalSetAllocateCopy32).1 ≠ none ∧
      (evaluateHOLFiniteState state journalSetAllocateCopy32).2.clock = state.clock - 2 at failed
    exact ⟨by rw [failed.2]; omega,by rw [failed.2]; omega,failed.1,noTimeout⟩

#print axioms RollbackWorld.journal_set_allocate_copy_all_requests
end InitECandidate.Runtime
