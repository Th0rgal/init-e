import InitECandidate.Runtime.HashNewHeapSafePlan
import InitECandidate.Runtime.HashNewReady
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- The original constructor establishes its complete table invariant
from the actual safe allocation plan, including near-limit successes. -/
theorem evaluate_htabNew_arrays_invariant_of_safe_plan {F : Type} (state : PanSemStateFiniteExact 64 F)
    (keyArgument capacityArgument : ExpHOL 64) (table keyLength capacity : BitVec 64) (bits : Nat)
    (arguments : evalListHOLFinite state
      (h := fun address => Classical.propDecidable (state.memaddrs address)) [keyArgument,capacityArgument] =
        some [.val (.word keyLength),.val (.word capacity)])
    (power : capacity.toNat = 2 ^ bits)
    (tableDomain : ∀ address : BitVec 64, table.toNat ≤ address.toNat →
      address.toNat < (htabNewOrderPos table keyLength capacity).toNat + capacity.toNat * 8 → state.memaddrs address)
    (code : state.code = originalRuntimeCode) (ticks : capacity.toNat + 8 ≤ state.clock)
    (heap : state.globals.lookup (ofString "heap_ptr") = some (.val (.word table)))
    (keyBound : keyLength.toNat ≤ 52) (tableAligned : table.toNat % 8 = 0)
    (pointerBound : table.toNat ≤ 33806089496)
    (fullSafe : AllocationPlanSafe table (htabNewAllocationSizes keyLength capacity))
    (headerDomain : ∀ offset : Nat, offset ≤ 64 → state.memaddrs (table + BitVec.ofNat 64 offset))
    (wordDomain : ∀ offset : Nat, offset < capacity.toNat →
      state.memaddrs (htabNewUsed table keyLength capacity + BitVec.ofNat 64 offset))
    (byteDomain : ∀ offset : Nat, offset < capacity.toNat →
      state.memaddrs (panByteAlignHOL (htabNewUsed table keyLength capacity + BitVec.ofNat 64 offset))) :
    ∃ ready, evaluateHOLFiniteState state
        (.call (some (none,none)) (ofString "htab_new") [keyArgument,capacityArgument]) = (none,ready) ∧
      hashOccupiedCount capacity (hashOccupancyRead ready (htabNewUsed table keyLength capacity)) = 0 ∧
      state.clock ≤ ready.clock + capacity.toNat + 8 ∧ ready.clock ≤ state.clock ∧
      ready.locals = state.locals ∧ ready.code = state.code ∧ ready.memaddrs = state.memaddrs ∧ ready.be = state.be ∧
      HashTableArraysInvariant keyLength table (allocationEnd table 72) (allocationEnd 0 keyLength) capacity
        (htabNewUsed table keyLength capacity) (htabNewValues table keyLength capacity) (htabNewOrder table keyLength capacity)
        (htabNewOrderPos table keyLength capacity) 0 bits ready ∧
      ∀ name continuation,
        evaluateHOLFiniteState state (.decCall name .one (ofString "htab_new") [keyArgument,capacityArgument] continuation) =
          (let output := evaluateHOLFiniteState (setVarHOLFinite name (.val (.word table)) ready) continuation;
           (output.1,{output.2 with locals := (HolFiniteMapExact.resVarEq output.2.locals
             (name,state.locals.lookup name))})) := by
  obtain ⟨ready,run,empty,cost,remaining,locals,postCode,addresses,endian,
      keyField,strideField,capField,countField,keysField,valuesField,usedField,orderField,reverseField,decl⟩ :=
    evaluate_htabNew_header_call_and_declaration_of_safe_plan state keyArgument capacityArgument table keyLength capacity
      arguments code ticks heap pointerBound tableAligned fullSafe headerDomain wordDomain byteDomain
  refine ⟨ready,run,empty,cost,remaining,locals,postCode,addresses,endian,?_,decl⟩
  obtain ⟨va,ua,oa,ra,hv,vu,uo,orr,limit⟩ := htabNew_insertion_layout_of_safe_plan table keyLength capacity pointerBound fullSafe
  obtain ⟨ka,sa,fits,hk,ku⟩ := htabNew_key_layout_of_safe_plan table keyLength capacity keyBound pointerBound fullSafe
  exact {
    keysAligned := ka
    strideAligned := sa
    valuesAligned := va
    usedAligned := ua
    orderAligned := oa
    orderPosAligned := ra
    headerKeys := hk
    headerValues := hv
    keysBefore := ku
    valuesBefore := vu
    usedBefore := uo
    orderBefore := orr
    endBound := limit
    fits := fits
    code := postCode.trans code
    power := power
    domain := by rw [addresses]; exact tableDomain
    cell0 := keyField
    cell8 := strideField
    cell16 := capField
    cell24 := countField
    cell32 := keysField
    cell40 := valuesField
    cell48 := usedField
    cell56 := orderField
    cell64 := reverseField
    agreement := empty.symm
    room := by change 0 < capacity.toNat; rw [power]; exact Nat.two_pow_pos bits
  }

/-- The original constructor establishes its complete table invariant
from the actual safe allocation plan, including near-limit successes. -/
theorem evaluate_htabNew_ready_of_safe_plan {F : Type} (state : PanSemStateFiniteExact 64 F)
    (keyArgument capacityArgument : ExpHOL 64) (table keyLength capacity : BitVec 64) (bits : Nat)
    (arguments : evalListHOLFinite state
      (h := fun address => Classical.propDecidable (state.memaddrs address)) [keyArgument,capacityArgument] =
        some [.val (.word keyLength),.val (.word capacity)])
    (power : capacity.toNat = 2 ^ bits)
    (tableDomain : ∀ address : BitVec 64, table.toNat ≤ address.toNat →
      address.toNat < (htabNewOrderPos table keyLength capacity).toNat + capacity.toNat * 8 → state.memaddrs address)
    (code : state.code = originalRuntimeCode) (ticks : capacity.toNat + 8 ≤ state.clock)
    (heap : state.globals.lookup (ofString "heap_ptr") = some (.val (.word table)))
    (keyBound : keyLength.toNat ≤ 52) (tableAligned : table.toNat % 8 = 0)
    (pointerBound : table.toNat ≤ 33806089496)
    (fullSafe : AllocationPlanSafe table (htabNewAllocationSizes keyLength capacity))
    (headerDomain : ∀ offset : Nat, offset ≤ 64 → state.memaddrs (table + BitVec.ofNat 64 offset))
    (wordDomain : ∀ offset : Nat, offset < capacity.toNat →
      state.memaddrs (htabNewUsed table keyLength capacity + BitVec.ofNat 64 offset))
    (byteDomain : ∀ offset : Nat, offset < capacity.toNat →
      state.memaddrs (panByteAlignHOL (htabNewUsed table keyLength capacity + BitVec.ofNat 64 offset))) :
    ∃ ready, evaluateHOLFiniteState state
        (.call (some (none,none)) (ofString "htab_new") [keyArgument,capacityArgument]) = (none,ready) ∧
      hashOccupiedCount capacity (hashOccupancyRead ready (htabNewUsed table keyLength capacity)) = 0 ∧
      state.clock ≤ ready.clock + capacity.toNat + 8 ∧ ready.clock ≤ state.clock ∧
      ready.locals = state.locals ∧ ready.code = state.code ∧ ready.memaddrs = state.memaddrs ∧ ready.be = state.be ∧
      HashTableReady keyLength table (allocationEnd table 72) (allocationEnd 0 keyLength) capacity
        (htabNewUsed table keyLength capacity) (htabNewValues table keyLength capacity) (htabNewOrder table keyLength capacity)
        (htabNewOrderPos table keyLength capacity) 0 bits
        (allocationEnd (htabNewOrderPos table keyLength capacity) (capacity * 8)) ready ∧
      ∀ name continuation,
        evaluateHOLFiniteState state (.decCall name .one (ofString "htab_new") [keyArgument,capacityArgument] continuation) =
          (let output := evaluateHOLFiniteState (setVarHOLFinite name (.val (.word table)) ready) continuation;
           (output.1,{output.2 with locals := (HolFiniteMapExact.resVarEq output.2.locals
             (name,state.locals.lookup name))})) := by
  obtain ⟨ready,run,empty,cost,remaining,locals,postCode,domain,endian,arrays,decl⟩ :=
    evaluate_htabNew_arrays_invariant_of_safe_plan state keyArgument capacityArgument table keyLength capacity bits arguments power tableDomain code ticks heap
      keyBound tableAligned pointerBound fullSafe headerDomain wordDomain byteDomain
  obtain ⟨checked,checkedRun,_,_,_,_,_,_,_,heapAfter,_⟩ :=
    evaluate_htabNew_header_call_and_declaration_heap_of_safe_plan state keyArgument capacityArgument table keyLength capacity arguments code ticks heap
      pointerBound tableAligned fullSafe headerDomain wordDomain byteDomain
  have same : ready = checked := congrArg Prod.snd (run.symm.trans checkedRun)
  have finalHeap : ready.globals.lookup (ofString "heap_ptr") = some (.val (.word (allocationEnd (htabNewOrderPos table keyLength capacity) (capacity * 8)))) := by
    rw [same]
    exact heapAfter
  have frontier := htabNew_frontier_facts_of_safe_plan table keyLength capacity pointerBound fullSafe
  have entries := hashEmpty_entry_invariants ready (htabNewUsed table keyLength capacity) (htabNewValues table keyLength capacity)
    (htabNewOrderPos table keyLength capacity) capacity empty
  exact ⟨ready,run,empty,cost,remaining,locals,postCode,domain,endian,
    ⟨⟨arrays,HashOrderEntriesBound.empty _ _ _,⟨finalHeap,frontier.1,frontier.2.1,frontier.2.2⟩⟩,
      entries.1,entries.2,HashOrderLinked.empty ready (htabNewUsed table keyLength capacity) (htabNewOrder table keyLength capacity)
        (htabNewOrderPos table keyLength capacity) capacity empty,htabNew_keys_before_values_of_safe_plan table keyLength capacity keyBound fullSafe⟩,decl⟩

#print axioms evaluate_htabNew_arrays_invariant_of_safe_plan
#print axioms evaluate_htabNew_ready_of_safe_plan
end InitECandidate.Runtime
