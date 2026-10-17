import InitECandidate.Runtime.RollbackWorldRegisteredSetSuccessHeapFrame
import InitECandidate.Runtime.HashTableReadySetCallRecordFrameSupported
import InitECandidate.Runtime.HashTableSetCallNoGrowthPhysicalFrameSupported
import InitECandidate.Runtime.HashTableReadySetUnsafeGrowthCallFrameDichotomy
import InitECandidate.Runtime.StateFreshTxFieldsRecordFrame
import InitECandidate.Runtime.StateFreshTxFieldsTableFrame
import InitECandidate.Runtime.RollbackWorldRegisteredSetBound
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- Every successful registered set call preserves the transaction table fields,
including growth and successful lookups with unsafe allocation plans. -/
theorem RollbackWorld.registered_set_success_fields {F : Type} (state : PanSemStateFiniteExact 64 F)
    (widths : BitVec 64 → BitVec 64) (tables : Set (BitVec 64))
    (journal snapshot count table key value : BitVec 64)
    (world : RollbackWorld widths tables journal snapshot count state)
    (_separated : RollbackPhysicalSeparated widths tables state) (member : table ∈ tables)
    (supported : widths table = 20 ∨ widths table = 32 ∨ widths table = 52)
    (ts fieldPointer : BitVec 64)
    (fields : StateFreshTxFields ts fieldPointer stateFreshTxAllTables state)
    (headerBefore : ts.toNat + 72 ≤ table.toNat)
    (ticks : 2 ^ 72 + 1 ≤ state.clock)
    (heapDomain : ∀ address : BitVec 64, address.toNat < 33806089496 → state.memaddrs address)
    (tableArgument keyArgument valueArgument : ExpHOL 64)
    (args : evalListHOLFinite state (h := fun address => Classical.propDecidable (state.memaddrs address))
      [tableArgument,keyArgument,valueArgument] = some [.val (.word table),.val (.word key),.val (.word value)])
    (aligned : key.toNat % 8 = 0)
    (words : ∀ offset : Nat, offset < (widths table).toNat → state.memaddrs (key + BitVec.ofNat 64 offset))
    (bytes : ∀ offset : Nat, offset < (widths table).toNat → state.memaddrs (panByteAlignHOL (key + BitVec.ofNat 64 offset)))
    (success : (evaluateHOLFiniteState state (.call (some (none,none)) (ofString "htab_set") [tableArgument,keyArgument,valueArgument])).1 = none) :
    StateFreshTxFields ts fieldPointer stateFreshTxAllTables (evaluateHOLFiniteState state (.call (some (none,none)) (ofString "htab_set") [tableArgument,keyArgument,valueArgument])).2 := by
  obtain ⟨pointer,keys,stride,capacity,used,values,order,reverse,items,bits,ready,small,large⟩ := world.ready table member
  have capacityBound : capacity.toNat ≤ 33806089496 := by
    have := ready.live.arrays.usedBefore
    have := ready.live.arrays.orderBefore
    have := ready.live.arrays.endBound
    omega
  have ceiling := hashSetRegistryCost_le_ceiling capacity (widths table) items capacityBound supported (Nat.le_of_lt ready.live.arrays.room)
  have numeric : 2 * capacity.toNat + 2 * (capacity * 2).toNat + (widths table).toNat + 13 +
      items.toNat * ((capacity * 2).toNat + (widths table).toNat + 4) ≤ state.clock := by
    unfold hashSetRegistryCost at ceiling
    omega
  have headerKeys := ready.live.arrays.headerKeys
  have headerValues := ready.live.arrays.headerValues
  have keysBefore := ready.live.arrays.keysBefore
  have valuesBefore := ready.live.arrays.valuesBefore
  have usedBefore := ready.live.arrays.usedBefore
  have orderBefore := ready.live.arrays.orderBefore
  have allocated := ready.live.frontier.allocated
  by_cases below : (items.toNat + 1) * 2 ≤ capacity.toNat
  · obtain ⟨_,post,_,run,_,frame,_⟩ := ready.set_call_no_growth_with_physical_frame state (widths table) table pointer keys stride capacity used values order reverse items key value bits supported
      aligned words bytes below (by omega) tableArgument keyArgument valueArgument args
    rw [run]
    exact fields.after_table_physical_frame state post ts fieldPointer (widths table) table pointer keys stride capacity used values order reverse items bits ready headerBefore frame
  · by_cases safePlan : AllocationPlanSafe pointer (htabGrowAllocationSizes capacity stride)
    · have domain : ∀ address : BitVec 64, table.toNat ≤ address.toNat →
          address.toNat < (htabGrowOrderPos pointer capacity stride).toNat + (capacity * 2).toNat * 8 → state.memaddrs address := by
        intro address lower upper
        obtain ⟨_,_,_,_,_,_,_,_,_,_,_,limit⟩ := htabGrow_array_layout_from_safe_plan table pointer capacity stride small ready.live.frontier.aligned (by omega) ready.live.frontier.bounded capacityBound safePlan
        exact heapDomain address (by omega)
      have start : (ts + (8 : BitVec 64)).toNat = ts.toNat + 8 := by
        rw [BitVec.toNat_add_of_lt (by change ts.toNat + 8 < 2 ^ 64; have := ready.live.frontier.bounded; omega)]
        rfl
      obtain ⟨post,run,_,_,_,_,_,_,_,frame⟩ := ready.set_call_supported_record_frame state (widths table) table pointer keys stride capacity used values order reverse items key value bits supported
        small ready.live.frontier.aligned ready.live.frontier.bounded capacityBound safePlan numeric ready.live.frontier.heap domain
        tableArgument keyArgument valueArgument args large aligned words bytes (ts + 8) 2
        (by omega) (by omega) (by omega) (Or.inl (by omega))
      rw [run]
      exact fields.after_two_record_frame frame
    · rcases ready.set_unsafe_growth_call_frame_dichotomy state (widths table) table pointer keys stride capacity used values order reverse items key value bits supported
        tableArgument keyArgument valueArgument args aligned words bytes (by omega) ready.live.frontier.heap ready.live.frontier.bounded safePlan (by omega) with good | failure
      · obtain ⟨post,run,_,_,_,_,_,_,_,_,frame⟩ := good
        rw [run]
        exact fields.after_table_physical_frame state post ts fieldPointer (widths table) table pointer keys stride capacity used values order reverse items bits ready headerBefore frame
      · exact False.elim (failure.1 success)

#print axioms RollbackWorld.registered_set_success_fields
end InitECandidate.Runtime
