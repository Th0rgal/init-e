import InitECandidate.Runtime.HashNewFrontierFacts
import InitECandidate.Runtime.HashNewInvariantHeap32
import InitECandidate.Runtime.HashTableConstructorArrays32
import InitECandidate.Runtime.HashOrderEntriesBound
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

theorem evaluate_htabNew_arrays_order_frontier32 {F : Type} (state : PanSemStateFiniteExact 64 F)
    (keyArgument capacityArgument : ExpHOL 64) (table capacity : BitVec 64) (bits : Nat)
    (arguments : evalListHOLFinite state
      (h := fun address => Classical.propDecidable (state.memaddrs address)) [keyArgument,capacityArgument] =
        some [.val (.word (32 : BitVec 64)),.val (.word capacity)])
    (power : capacity.toNat = 2 ^ bits)
    (tableDomain : ∀ address : BitVec 64, table.toNat ≤ address.toNat →
      address.toNat < (htabNewOrderPos table 32 capacity).toNat + capacity.toNat * 8 → state.memaddrs address)
    (code : state.code = originalRuntimeCode) (ticks : capacity.toNat + 8 ≤ state.clock)
    (heap : state.globals.lookup (ofString "heap_ptr") = some (.val (.word table)))
    (keyBound : (32 : BitVec 64).toNat ≤ 52) (tableAligned : table.toNat % 8 = 0)
    (budget : table.toNat + 81 * capacity.toNat + 114 ≤ 33806089496)
    (headerDomain : ∀ offset : Nat, offset ≤ 64 → state.memaddrs (table + BitVec.ofNat 64 offset))
    (wordDomain : ∀ offset : Nat, offset < capacity.toNat →
      state.memaddrs (htabNewUsed table (32 : BitVec 64) capacity + BitVec.ofNat 64 offset))
    (byteDomain : ∀ offset : Nat, offset < capacity.toNat →
      state.memaddrs (panByteAlignHOL (htabNewUsed table (32 : BitVec 64) capacity + BitVec.ofNat 64 offset))) :
    ∃ ready, evaluateHOLFiniteState state
        (.call (some (none,none)) (ofString "htab_new") [keyArgument,capacityArgument]) = (none,ready) ∧
      hashOccupiedCount capacity (hashOccupancyRead ready (htabNewUsed table (32 : BitVec 64) capacity)) = 0 ∧
      state.clock ≤ ready.clock + capacity.toNat + 8 ∧ ready.clock ≤ state.clock ∧
      ready.locals = state.locals ∧ ready.code = state.code ∧ ready.memaddrs = state.memaddrs ∧ ready.be = state.be ∧
      ready.globals.lookup (ofString "heap_ptr") = some (.val (.word (allocationEnd (htabNewOrderPos table 32 capacity) (capacity * 8)))) ∧
      (htabNewOrderPos table 32 capacity).toNat + capacity.toNat * 8 ≤ (allocationEnd (htabNewOrderPos table 32 capacity) (capacity * 8)).toNat ∧
      (allocationEnd (htabNewOrderPos table 32 capacity) (capacity * 8)).toNat ≤ 33806089496 ∧
      (allocationEnd (htabNewOrderPos table 32 capacity) (capacity * 8)).toNat % 8 = 0 ∧
      HashTableArraysInvariant32 table (allocationEnd table 72) (allocationEnd 0 32) capacity
        (htabNewUsed table 32 capacity) (htabNewValues table 32 capacity) (htabNewOrder table 32 capacity)
        (htabNewOrderPos table 32 capacity) 0 bits ready ∧
      HashOrderEntriesBound (htabNewOrder table 32 capacity) capacity 0 ready ∧
      ∀ name continuation,
        evaluateHOLFiniteState state (.decCall name .one (ofString "htab_new") [keyArgument,capacityArgument] continuation) =
          (let output := evaluateHOLFiniteState (setVarHOLFinite name (.val (.word table)) ready) continuation;
           (output.1,{output.2 with locals := (HolFiniteMapExact.resVarEq output.2.locals
             (name,state.locals.lookup name))})) := by
  obtain ⟨ready,run,empty,cost,remaining,locals,postCode,addresses,endian,heapAfter,valid,decl⟩ :=
    evaluate_htabNew_invariant32_heap state keyArgument capacityArgument table capacity bits arguments power tableDomain code ticks heap
      keyBound tableAligned budget headerDomain wordDomain byteDomain
  have frontier := htabNew_frontier_facts table 32 capacity keyBound budget
  exact ⟨ready,run,empty,cost,remaining,locals,postCode,addresses,endian,heapAfter,frontier.1,frontier.2.1,frontier.2.2,
    valid.arrays ready table capacity 0 bits,HashOrderEntriesBound.empty _ _ _,decl⟩

#print axioms evaluate_htabNew_arrays_order_frontier32
end InitECandidate.Runtime
