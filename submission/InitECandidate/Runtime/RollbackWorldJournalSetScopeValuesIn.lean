import InitECandidate.Runtime.HashTableValuesInJournalSetReserved
import InitECandidate.Runtime.RollbackWorldRegisteredSet
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- Registered pointer tables retain their values through the actual record
scope without caller-supplied hash-array geometry or safe-plan assumptions. -/
theorem RollbackWorld.journal_set_record_scope_values_in {F : Type} {widths : BitVec 64 → BitVec 64} {tables : Set (BitVec 64)}
    {journal snapshot count : BitVec 64} {state : PanSemStateFiniteExact 64 F}
    (world : RollbackWorld widths tables journal snapshot count state)
    (table key present value : BitVec 64) (member : table ∈ tables)
    (space : count.toNat < 524288)
    (journalBound : journal.toNat + 524288 * 32 ≤ 33806089496)
    (journalAligned : journal.toNat % 8 = 0)
    (journalHeaders : ∀ other ∈ tables, journal.toNat + 524288 * 32 ≤ other.toNat)
    (heapDomain : ∀ address : BitVec 64, address.toNat < 33806089496 → state.memaddrs address)
    (supported : widths table = 20 ∨ widths table = 32 ∨ widths table = 52)
    (t : state.locals.lookup (ofString "t") = some (.val (.word table)))
    (kc : state.locals.lookup (ofString "kc") = some (.val (.word key)))
    (old : state.locals.lookup (ofString "old") = some (.rStruct [.val (.word present),.val (.word value)]))
    (originalKey newValue : BitVec 64)
    (keyLocal : state.locals.lookup (ofString "key") = some (.val (.word originalKey)))
    (valueLocal : state.locals.lookup (ofString "value") = some (.val (.word newValue)))
    (originalAligned : originalKey.toNat % 8 = 0)
    (originalWords : ∀ offset : Nat, offset < (widths table).toNat → state.memaddrs (originalKey + BitVec.ofNat 64 offset))
    (originalBytes : ∀ offset : Nat, offset < (widths table).toNat → state.memaddrs (panByteAlignHOL (originalKey + BitVec.ofNat 64 offset)))
    (targets : Set (BitVec 64)) (registered : HashTableValuesIn table targets state) (newMember : newValue ∈ targets)
    (ticks : 2 ^ 74 ≤ state.clock) :
    (evaluateHOLFiniteState state journalSetRecordScope32).1 ≠ some .timeOut ∧
    state.clock ≤ (evaluateHOLFiniteState state journalSetRecordScope32).2.clock + 2 ^ 74 ∧
    (evaluateHOLFiniteState state journalSetRecordScope32).2.clock ≤ state.clock ∧
    (∀ result : ValueHOL 64, (evaluateHOLFiniteState state journalSetRecordScope32).1 = some (.returned result) →
      HashTableValuesIn table targets (evaluateHOLFiniteState state journalSetRecordScope32).2) := by
  obtain ⟨pointer,keys,stride,capacity,used,values,order,reverse,items,bits,ready,small,large⟩ := world.ready table member
  have capacityBound : capacity.toNat ≤ 33806089496 := by
    have := ready.live.arrays.usedBefore
    have := ready.live.arrays.orderBefore
    have := ready.live.arrays.endBound
    omega
  have headerBefore : table.toNat + 72 ≤ pointer.toNat := by
    have := ready.live.arrays.headerKeys
    have := ready.live.arrays.keysBefore
    have := ready.live.arrays.usedBefore
    have := ready.live.arrays.orderBefore
    have := ready.live.frontier.allocated
    omega
  have domain : AllocationPlanSafe pointer (htabGrowAllocationSizes capacity stride) →
      ∀ address : BitVec 64, table.toNat ≤ address.toNat → address.toNat < (htabGrowOrderPos pointer capacity stride).toNat + (capacity * 2).toNat * 8 → state.memaddrs address := by
    intro safePlan address lower upper
    obtain ⟨_,_,_,_,_,_,_,_,_,_,_,limit⟩ := htabGrow_array_layout_from_safe_plan table pointer capacity stride small ready.live.frontier.aligned headerBefore ready.live.frontier.bounded capacityBound safePlan
    exact heapDomain address (by omega)
  have outcome := ready.journal_set_record_reserved_values_in state (widths table) table pointer keys stride capacity used values order reverse items originalKey newValue bits supported
    targets registered newMember small ticks domain journal key present value count space journalBound journalAligned (journalHeaders table member)
    (by intro address lower upper; exact heapDomain address (by omega))
    t kc old keyLocal valueLocal world.journalGlobal world.counter large originalAligned originalWords originalBytes
  rcases outcome with success | failure
  · obtain ⟨post,run,_,postRegistered,cost,remaining,_,_,_⟩ := success
    rw [run]
    exact ⟨by simp,cost,remaining,fun _ _ => postRegistered⟩
  · obtain ⟨_,noTimeout,noReturn,_,cost,remaining⟩ := failure
    exact ⟨noTimeout,cost,remaining,fun result success => False.elim (noReturn result success)⟩

#print axioms RollbackWorld.journal_set_record_scope_values_in
end InitECandidate.Runtime
