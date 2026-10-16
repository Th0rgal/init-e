import InitECandidate.Runtime.HashNewHeaderCallHeap
import InitECandidate.Runtime.HashTableInvariant32
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- The actual original constructor establishes the reusable table invariant. -/
theorem evaluate_htabNew_invariant32_heap {F : Type} (state : PanSemStateFiniteExact 64 F)
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
      HashTableInvariant32 table capacity 0 bits ready ∧
      ∀ name continuation,
        evaluateHOLFiniteState state (.decCall name .one (ofString "htab_new") [keyArgument,capacityArgument] continuation) =
          (let output := evaluateHOLFiniteState (setVarHOLFinite name (.val (.word table)) ready) continuation;
           (output.1,{output.2 with locals := (HolFiniteMapExact.resVarEq output.2.locals
             (name,state.locals.lookup name))})) := by
  obtain ⟨ready,run,empty,cost,remaining,locals,postCode,addresses,endian,heapAfter,
      keyField,strideField,capField,countField,keysField,valuesField,usedField,orderField,reverseField,decl⟩ :=
    evaluate_htabNew_header_call_and_declaration_heap state keyArgument capacityArgument table 32 capacity
      arguments code ticks heap keyBound tableAligned budget headerDomain wordDomain byteDomain
  refine ⟨ready,run,empty,cost,remaining,locals,postCode,addresses,endian,heapAfter,?_,decl⟩
  exact {
    code := postCode.trans code
    power := power
    heapBudget := budget
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

#print axioms evaluate_htabNew_invariant32_heap
end InitECandidate.Runtime
