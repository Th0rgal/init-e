import InitECandidate.Runtime.HashGrowHeaderLoads
import InitECandidate.Runtime.HashGrowKeysHeapWidth
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- The complete original growth prefix through rehash entry: real header
loads, doubling, five allocations, zeroing and all header stores. -/
theorem evaluate_htabGrow_prefix_width_heap {F : Type} (state : PanSemStateFiniteExact 64 F)
    (keyLength table pointer capacity stride keys values order count : BitVec 64) (bits : Nat) (continuation : ProgHOL 64)
    (code : state.code = originalRuntimeCode) (power : capacity.toNat = 2 ^ bits)
    (strideAligned : stride.toNat % 8 = 0) (fits : keyLength.toNat ≤ stride.toNat) (strideBound : stride.toNat ≤ 56)
    (pointerAligned : pointer.toNat % 8 = 0) (headerBefore : table.toNat + 72 ≤ pointer.toNat)
    (pointerBound : pointer.toNat ≤ 33806089496)
    (capacityBound : capacity.toNat ≤ 33806089496)
    (safePlan : AllocationPlanSafe pointer (htabGrowAllocationSizes capacity stride))
    (ticks : (capacity * 2).toNat + 6 ≤ state.clock)
    (heap : state.globals.lookup (ofString "heap_ptr") = some (.val (.word pointer)))
    (domain : ∀ address : BitVec 64, table.toNat ≤ address.toNat →
      address.toNat < (htabGrowOrderPos pointer capacity stride).toNat + (capacity * 2).toNat * 8 → state.memaddrs address)
    (tableLocal : state.locals.lookup (ofString "t") = some (.val (.word table)))
    (keyField : state.memory (table + 0) = .word keyLength)
    (cell16 : state.memory (table + 16) = .word capacity)
    (cell8 : state.memory (table + 8) = .word stride)
    (cell32 : state.memory (table + 32) = .word keys)
    (cell40 : state.memory (table + 40) = .word values)
    (cell56 : state.memory (table + 56) = .word order)
    (cell24 : state.memory (table + 24) = .word count)
    : ∃ ready, evaluateHOLFiniteState state (hashGrowHeaderLoads (hashGrowKeysAllocation continuation)) =
      (let output := evaluateHOLFiniteState ready continuation;
       (output.1,{output.2 with locals := (restoreGrowthLocals state.locals [ofString "cap",ofString "stride",ofString "keys",ofString "vals",ofString "order",ofString "nitems",ofString "ncap"]
         (restoreGrowthLocals state.locals [ofString "nkeys",ofString "nvals",ofString "nused",ofString "norder",ofString "norder_pos"] output.2.locals))})) ∧
      HashTableArraysInvariant keyLength table pointer stride (capacity * 2) (htabGrowUsed pointer capacity stride)
        (htabGrowValues pointer capacity stride) (htabGrowOrder pointer capacity stride)
        (htabGrowOrderPos pointer capacity stride) 0 (bits + 1) ready ∧
      state.clock ≤ ready.clock + (capacity * 2).toNat + 6 ∧ ready.clock ≤ state.clock ∧
      ready.code = state.code ∧ ready.memaddrs = state.memaddrs ∧ ready.be = state.be ∧
      ready.globals.lookup (ofString "heap_ptr") = some (.val (.word
        (allocationEnd (htabGrowOrderPos pointer capacity stride) ((capacity * 2) * 8)))) ∧
      ready.locals.lookup (ofString "t") = some (.val (.word table)) ∧
      ready.locals.lookup (ofString "keys") = some (.val (.word keys)) ∧
      ready.locals.lookup (ofString "stride") = some (.val (.word stride)) ∧
      ready.locals.lookup (ofString "vals") = some (.val (.word values)) ∧
      ready.locals.lookup (ofString "order") = some (.val (.word order)) ∧
      ready.locals.lookup (ofString "nitems") = some (.val (.word count)) ∧
      (∀ name, name ∉ [ofString "cap",ofString "stride",ofString "keys",ofString "vals",ofString "order",ofString "nitems",ofString "ncap",ofString "nkeys",ofString "nvals",ofString "nused",ofString "norder",ofString "norder_pos"] → ready.locals.lookup name = state.locals.lookup name) ∧
      (∀ watched : BitVec 64, table.toNat + 72 ≤ watched.toNat → watched.toNat < pointer.toNat →
        ready.memory watched = state.memory watched) := by
  obtain ⟨_,_,_,_,_,_,_,_,_,_,_,limit⟩ := htabGrow_array_layout_from_safe_plan table pointer capacity stride strideBound pointerAligned headerBefore pointerBound capacityBound safePlan
  have headerDomain : ∀ offset : Nat, offset ≤ 64 → state.memaddrs (table + BitVec.ofNat 64 offset) := by
    intro offset small
    have natural : (BitVec.ofNat 64 offset).toNat = offset := by
      change offset % 2 ^ 64 = offset
      exact Nat.mod_eq_of_lt (by omega)
    have address : (table + BitVec.ofNat 64 offset).toNat = table.toNat + offset := by
      rw [BitVec.toNat_add_of_lt (by rw [natural]; omega),natural]
    apply domain <;> omega
  obtain ⟨loaded,loads,capBinding,strideBinding,keysBinding,valsBinding,orderBinding,countBinding,nextBinding,
      memory,globals,postCode,addresses,endian,clock,oldOther⟩ :=
    evaluate_htabGrow_header_loads state table capacity stride keys values order count tableLocal
      (headerDomain 16 (by decide)) cell16
      (headerDomain 8 (by decide)) cell8
      (headerDomain 32 (by decide)) cell32
      (headerDomain 40 (by decide)) cell40
      (headerDomain 56 (by decide)) cell56
      (headerDomain 24 (by decide)) cell24
  have t : loaded.locals.lookup (ofString "t") = some (.val (.word table)) :=
    (oldOther _ (by decide)).trans tableLocal
  obtain ⟨ready,allocations,valid,cost,remaining,lastCode,lastAddresses,lastEndian,lastHeap,newOther,newFrame⟩ :=
    evaluate_htabGrow_keys_allocation_width_heap loaded keyLength table pointer capacity stride bits continuation (postCode.trans code) power
      strideAligned fits strideBound pointerAligned headerBefore pointerBound capacityBound safePlan (by rw [clock]; exact ticks)
      (by rw [addresses]; exact domain) (by rw [memory]; exact keyField) (by rw [memory]; exact cell8)
      t nextBinding strideBinding (by rw [globals]; exact heap)
  have saved : ∀ locals, restoreGrowthLocals loaded.locals [ofString "nkeys",ofString "nvals",ofString "nused",ofString "norder",ofString "norder_pos"] locals =
      restoreGrowthLocals state.locals [ofString "nkeys",ofString "nvals",ofString "nused",ofString "norder",ofString "norder_pos"] locals := by
    intro locals
    apply restoreGrowthLocals_congr
    intro name member
    apply oldOther
    simp at member
    rcases member with rfl | rfl | rfl | rfl | rfl <;> decide
  rw [loads,allocations]
  refine ⟨ready,?_,valid,?_,?_,lastCode.trans postCode,lastAddresses.trans addresses,lastEndian.trans endian,lastHeap,
    (newOther (ofString "t") (by decide)).trans t,
    (newOther (ofString "keys") (by decide)).trans keysBinding,
    (newOther (ofString "stride") (by decide)).trans strideBinding,
    (newOther (ofString "vals") (by decide)).trans valsBinding,
    (newOther (ofString "order") (by decide)).trans orderBinding,
    (newOther (ofString "nitems") (by decide)).trans countBinding,
    ?_,?_⟩
  · dsimp only
    rw [saved]
  · rw [clock] at cost
    exact cost
  · rw [clock] at remaining
    exact remaining
  · intro name outside
    have oldOutside : name ∉ [ofString "cap",ofString "stride",ofString "keys",ofString "vals",ofString "order",ofString "nitems",ofString "ncap"] := by
      intro member
      apply outside
      change name ∈ [ofString "cap",ofString "stride",ofString "keys",ofString "vals",ofString "order",ofString "nitems",ofString "ncap"] ++ [ofString "nkeys",ofString "nvals",ofString "nused",ofString "norder",ofString "norder_pos"]
      exact List.mem_append_left _ member
    have newOutside : name ∉ [ofString "nkeys",ofString "nvals",ofString "nused",ofString "norder",ofString "norder_pos"] := by
      intro member
      apply outside
      change name ∈ [ofString "cap",ofString "stride",ofString "keys",ofString "vals",ofString "order",ofString "nitems",ofString "ncap"] ++ [ofString "nkeys",ofString "nvals",ofString "nused",ofString "norder",ofString "norder_pos"]
      exact List.mem_append_right _ member
    exact (newOther name newOutside).trans (oldOther name oldOutside)
  · intro watched lower upper
    have preserved := newFrame watched lower upper
    rw [preserved,memory]

#print axioms evaluate_htabGrow_prefix_width_heap
end InitECandidate.Runtime
