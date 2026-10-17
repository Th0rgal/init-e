import InitECandidate.Runtime.HashTableValuesInPhysicalFrame
import InitECandidate.Runtime.HashGrowCallFrontierSupported
import InitECandidate.Runtime.HashGrowCallOutsideHeaderSupported
import InitECandidate.Runtime.HashTablePhysicalAdvanceFrame
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- Actual growth preserves a disjoint table on either side of its updated header. -/
theorem evaluate_htabGrow_other_values_in {F : Type} (state : PanSemStateFiniteExact 64 F)
    (keyLength table pointer capacity stride keys values order items : BitVec 64) (bits : Nat)
    (supported : keyLength = 20 ∨ keyLength = 32 ∨ keyLength = 52)
    (tableArgument : ExpHOL 64)
    (arguments : evalListHOLFinite state
      (h := fun address => Classical.propDecidable (state.memaddrs address)) [tableArgument] = some [.val (.word table)])
    (code : state.code = originalRuntimeCode) (power : capacity.toNat = 2 ^ bits)
    (old : HashGrowOldArrays table keys stride values order capacity items pointer.toNat state)
    (strideAligned : stride.toNat % 8 = 0) (fits : keyLength.toNat ≤ stride.toNat) (strideBound : stride.toNat ≤ 56)
    (pointerAligned : pointer.toNat % 8 = 0) (headerBefore : table.toNat + 72 ≤ pointer.toNat)
    (pointerBound : pointer.toNat ≤ 33806089496)
    (capacityBound : capacity.toNat ≤ 33806089496)
    (safePlan : AllocationPlanSafe pointer (htabGrowAllocationSizes capacity stride))
    (ticks : (capacity * 2).toNat + 7 + items.toNat * ((capacity * 2).toNat + keyLength.toNat + 4) ≤ state.clock)
    (heap : state.globals.lookup (ofString "heap_ptr") = some (.val (.word pointer)))
    (domain : ∀ address : BitVec 64, table.toNat ≤ address.toNat →
      address.toNat < (htabGrowOrderPos pointer capacity stride).toNat + (capacity * 2).toNat * 8 → state.memaddrs address)
    (keyField : state.memory (table + 0) = .word keyLength)
    (cell16 : state.memory (table + 16) = .word capacity)
    (cell8 : state.memory (table + 8) = .word stride)
    (cell32 : state.memory (table + 32) = .word keys)
    (cell40 : state.memory (table + 40) = .word values)
    (cell56 : state.memory (table + 56) = .word order)
    (cell24 : state.memory (table + 24) = .word items)
    (otherKeyLength otherTable otherKeys otherStride otherCapacity otherUsed otherValues otherOrder otherOrderPos otherItems : BitVec 64)
    (otherBits : Nat)
    (otherReady : HashTableReady otherKeyLength otherTable otherKeys otherStride otherCapacity otherUsed otherValues otherOrder otherOrderPos otherItems otherBits pointer state)
    (targets : Set (BitVec 64)) (registered : HashTableValuesIn otherTable targets state)
    (separate : ∀ address : BitVec 64, table.toNat ≤ address.toNat → address.toNat < table.toNat + 72 →
      ¬tablePhysicalRegion otherTable otherKeys otherStride otherCapacity otherUsed otherValues otherOrder otherOrderPos address) :
    ∃ post, evaluateHOLFiniteState state (.call (some (none,none)) (ofString "htab_grow") [tableArgument]) = (none,post) ∧
      HashTableReady otherKeyLength otherTable otherKeys otherStride otherCapacity otherUsed otherValues otherOrder otherOrderPos otherItems otherBits
        (allocationEnd (htabGrowOrderPos pointer capacity stride) ((capacity * 2) * 8)) post ∧
      HashTableValuesIn otherTable targets post ∧
      state.clock ≤ post.clock + (capacity * 2).toNat + 7 + items.toNat * ((capacity * 2).toNat + keyLength.toNat + 4) ∧
      post.clock ≤ state.clock ∧ post.locals = state.locals ∧ post.code = state.code ∧ post.memaddrs = state.memaddrs ∧ post.be = state.be := by
  obtain ⟨post,run,valid,_,_,cost,remaining,locals,postCode,addresses,endian,postHeap,frontier,frame⟩ :=
    evaluate_htabGrow_supported_call_frontier state keyLength table pointer capacity stride keys values order items bits supported tableArgument arguments code power old
      strideAligned fits strideBound pointerAligned headerBefore pointerBound capacityBound safePlan ticks heap domain
      keyField cell16 cell8 cell32 cell40 cell56 cell24
  obtain ⟨checked,checkedRun,_,_,_,_,_,_,_,_,_,_,_,_,outsideFrame⟩ :=
    evaluate_htabGrow_supported_call_outside_header state keyLength table pointer capacity stride keys values order items bits supported tableArgument arguments code power old
      strideAligned fits strideBound pointerAligned headerBefore pointerBound capacityBound safePlan ticks heap domain
      keyField cell16 cell8 cell32 cell40 cell56 cell24
  have same : post = checked := congrArg Prod.snd (run.symm.trans checkedRun)
  rw [← same] at outsideFrame
  have monotone : pointer.toNat ≤ (allocationEnd (htabGrowOrderPos pointer capacity stride) ((capacity * 2) * 8)).toNat := by
    have ku := valid.keysBefore
    have uo := valid.usedBefore
    have oo := valid.orderBefore
    have allocated := frontier.allocated
    omega
  have otherFrame : ∀ address : BitVec 64,
      tablePhysicalRegion otherTable otherKeys otherStride otherCapacity otherUsed otherValues otherOrder otherOrderPos address →
      post.memory address = state.memory address := by
    intro address member
    have below := otherReady.physical_below_frontier state otherKeyLength otherTable pointer otherKeys otherStride otherCapacity otherUsed otherValues otherOrder otherOrderPos otherItems otherBits address member
    apply outsideFrame address ?_ below
    have notHeader : ¬(table.toNat ≤ address.toNat ∧ address.toNat < table.toNat + 72) := by
      intro inside
      exact separate address inside.1 inside.2 member
    omega
  exact ⟨post,run,otherReady.physical_frame_advance state post otherKeyLength otherTable pointer
    (allocationEnd (htabGrowOrderPos pointer capacity stride) ((capacity * 2) * 8)) otherKeys otherStride otherCapacity otherUsed otherValues otherOrder otherOrderPos otherItems otherBits
    otherFrame postHeap monotone frontier.bounded frontier.aligned postCode addresses endian,
    registered.physical_frame state post otherKeyLength otherTable otherKeys otherStride otherCapacity otherUsed otherValues otherOrder otherOrderPos otherItems otherBits otherReady.live.arrays targets otherFrame addresses endian,
    cost,remaining,locals,postCode,addresses,endian⟩

#print axioms evaluate_htabGrow_other_values_in
end InitECandidate.Runtime
