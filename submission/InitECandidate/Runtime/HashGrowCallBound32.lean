import InitECandidate.Runtime.HashGrowCallSafePlan32
import InitECandidate.Runtime.HashGrowFailureCall
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

theorem evaluate_htabGrow32_call_bounded {F : Type} (state : PanSemStateFiniteExact 64 F)
    (table pointer capacity stride keys values order items : BitVec 64) (bits : Nat)
    (tableArgument : ExpHOL 64)
    (arguments : evalListHOLFinite state
      (h := fun address => Classical.propDecidable (state.memaddrs address)) [tableArgument] = some [.val (.word table)])
    (code : state.code = originalRuntimeCode) (power : capacity.toNat = 2 ^ bits)
    (old : HashGrowOldArrays table keys stride values order capacity items pointer.toNat state)
    (strideAligned : stride.toNat % 8 = 0) (fits : 32 ≤ stride.toNat) (strideBound : stride.toNat ≤ 56)
    (pointerAligned : pointer.toNat % 8 = 0) (headerBefore : table.toNat + 72 ≤ pointer.toNat)
    (pointerBound : pointer.toNat ≤ 33806089496)
    (capacityBound : capacity.toNat ≤ 33806089496)
    (ticks : (capacity * 2).toNat + 7 + items.toNat * ((capacity * 2).toNat + 36) ≤ state.clock)
    (heap : state.globals.lookup (ofString "heap_ptr") = some (.val (.word pointer)))
    (domain : ∀ address : BitVec 64, table.toNat ≤ address.toNat →
      address.toNat < 33806089496 → state.memaddrs address)
    (keyField : state.memory (table + 0) = .word (32 : BitVec 64))
    (cell16 : state.memory (table + 16) = .word capacity)
    (cell8 : state.memory (table + 8) = .word stride)
    (cell32 : state.memory (table + 32) = .word keys)
    (cell40 : state.memory (table + 40) = .word values)
    (cell56 : state.memory (table + 56) = .word order)
    (cell24 : state.memory (table + 24) = .word items) :
    state.clock ≤ (evaluateHOLFiniteState state (.call (some (none,none)) (ofString "htab_grow") [tableArgument])).2.clock +
      (capacity * 2).toNat + 7 + items.toNat * ((capacity * 2).toNat + 36) ∧
    (evaluateHOLFiniteState state (.call (some (none,none)) (ofString "htab_grow") [tableArgument])).2.clock ≤ state.clock := by
  classical
  by_cases safe : AllocationPlanSafe pointer (htabGrowAllocationSizes capacity stride)
  · obtain ⟨_,_,_,_,_,_,_,_,_,_,_,limit⟩ := htabGrow_array_layout_from_safe_plan table pointer capacity stride
      strideBound pointerAligned headerBefore pointerBound capacityBound safe
    have allocatedDomain : ∀ address : BitVec 64, table.toNat ≤ address.toNat →
        address.toNat < (htabGrowOrderPos pointer capacity stride).toNat + (capacity * 2).toNat * 8 → state.memaddrs address := by
      intro address lower upper
      exact domain address lower (by omega)
    obtain ⟨post,run,_,_,_,cost,remaining,_⟩ := evaluate_htabGrow32_call_safe_plan state
      table pointer capacity stride keys values order items bits tableArgument arguments code power old strideAligned fits strideBound
      pointerAligned headerBefore pointerBound capacityBound safe ticks heap allocatedDomain keyField cell16 cell8 cell32 cell40 cell56 cell24
    rw [run]
    exact ⟨cost,remaining⟩
  · have headerDomain : ∀ offset : Nat, offset ≤ 64 → state.memaddrs (table + BitVec.ofNat 64 offset) := by
      intro offset small
      have natural : (BitVec.ofNat 64 offset).toNat = offset := by
        change offset % 2 ^ 64 = offset
        exact Nat.mod_eq_of_lt (by omega)
      have address : (table + BitVec.ofNat 64 offset).toNat = table.toNat + offset := by
        rw [BitVec.toNat_add_of_lt (by rw [natural]; omega),natural]
      apply domain <;> omega
    have failure := evaluate_htabGrow_allocation_failure_call state table capacity stride keys values order items
      (headerDomain 16 (by decide)) cell16 (headerDomain 8 (by decide)) cell8
      (headerDomain 32 (by decide)) cell32 (headerDomain 40 (by decide)) cell40
      (headerDomain 56 (by decide)) cell56 (headerDomain 24 (by decide)) cell24
      pointer code heap pointerBound (by omega) safe tableArgument arguments
    exact ⟨by have := failure.1; omega,failure.2⟩

#print axioms evaluate_htabGrow32_call_bounded
end InitECandidate.Runtime
