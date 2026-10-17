import InitECandidate.Runtime.RollbackWorldJournalSetAllRequestsValuesIn
import InitECandidate.Runtime.JournalSetGuardWidth
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- Successful journal-set returns preserve the enlarged world through the
original journal guard and temporary key-width scope. -/
theorem RollbackWorld.journal_set_after_get_room_values_in {F : Type} {widths : BitVec 64 → BitVec 64} {tables : Set (BitVec 64)}
    {journal snapshot count : BitVec 64} {state : PanSemStateFiniteExact 64 F}
    (world : RollbackWorld widths tables journal snapshot count state)
    (separated : RollbackPhysicalSeparated widths tables state)
    (witness : BitVec 64) (member : witness ∈ tables)
    (pointer source size : BitVec 64)
    (keyLocal : state.locals.lookup (ofString "key") = some (.val (.word source)))
    (code : state.code = originalRuntimeCode) (ticks : 2 ^ 74 + size.toNat + 2 ≤ state.clock)
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
    (heapDomain : ∀ address : BitVec 64, address.toNat < 33806089496 → state.memaddrs address)
    (capacityGlobal : state.globals.lookup (ofString "journal_cap") = some (.val (.word (524288 : BitVec 64))))
    (targets : Set (BitVec 64)) (registered : HashTableValuesIn witness targets state) (newMember : newValue ∈ targets)
    (returnedValue : ValueHOL 64)
    (success : (evaluateHOLFiniteState state journalSetAfterGet32).1 = some (.returned returnedValue)) :
    HashTableValuesIn witness targets (evaluateHOLFiniteState state journalSetAfterGet32).2 := by
  let entered := setVarHOLFinite (ofString "klen") (.val (.word size)) state
  have midWorld : RollbackWorld widths tables journal snapshot count entered := world.after_read rfl rfl rfl rfl rfl (by
    simp [entered,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,show ofString "klen" ≠ ofString "snap" from by decide])
  have midSep : RollbackPhysicalSeparated widths tables entered := separated.after_read rfl rfl rfl rfl rfl
  have locals : ∀ name, name ≠ ofString "klen" → entered.locals.lookup name = state.locals.lookup name := by
    intro name different
    simp [entered,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,Ne.symm different]
  have sizeLocal : entered.locals.lookup (ofString "klen") = some (.val (.word size)) := by
    simp [entered,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]
  obtain ⟨op,keys,stride,capacity,used,values,order,reverse,items,bits,ready,_,_⟩ := world.ready witness member
  have headerDomain := ready.live.arrays.header_domain state (widths witness) witness keys stride capacity used values order reverse items bits 0 (by decide)
  have headerCell : state.memory (witness + 0) = .word size := by simpa only [widthEq] using ready.live.arrays.cell0
  have guard := evaluate_journalSet_guard_width state size witness count 524288 tableLocal world.counter capacityGlobal space headerDomain headerCell
  have bodySuccess : (evaluateHOLFiniteState entered journalSetAllocateCopy32).1 = some (.returned returnedValue) :=
    (congrArg Prod.fst guard).symm.trans success
  have valid := midWorld.journal_set_allocate_copy_all_requests_values_in midSep witness member pointer source size
    ((locals (ofString "key") (by decide)).trans keyLocal) sizeLocal code ticks heap pointerBound aligned sourceAligned sourceWords sourceBytes
    present oldValue newValue widthEq supported ((locals (ofString "t") (by decide)).trans tableLocal)
    ((locals (ofString "old") (by decide)).trans oldLocal) ((locals (ofString "value") (by decide)).trans valueLocal)
    space journalBound journalAligned journalHeaders heapDomain targets (registered.after_read rfl rfl rfl) newMember returnedValue bodySuccess
  rw [guard]
  exact valid.after_read rfl rfl rfl

#print axioms RollbackWorld.journal_set_after_get_room_values_in
end InitECandidate.Runtime
