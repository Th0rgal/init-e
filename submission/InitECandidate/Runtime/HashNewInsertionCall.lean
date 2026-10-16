import InitECandidate.Runtime.HashNewHeaderCall
import InitECandidate.Runtime.HashNewInsertionMemory
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- The actual constructor call establishes the empty insertion environment. -/
theorem evaluate_htabNew_insertion_call_and_declaration {F : Type} (state : PanSemStateFiniteExact 64 F)
    (keyArgument capacityArgument : ExpHOL 64) (table keyLength capacity : BitVec 64)
    (arguments : evalListHOLFinite state
      (h := fun address => Classical.propDecidable (state.memaddrs address)) [keyArgument,capacityArgument] =
        some [.val (.word keyLength),.val (.word capacity)])
    (code : state.code = originalRuntimeCode) (ticks : capacity.toNat + 8 ≤ state.clock)
    (heap : state.globals.lookup (ofString "heap_ptr") = some (.val (.word table)))
    (keyBound : keyLength.toNat ≤ 52) (tableAligned : table.toNat % 8 = 0)
    (budget : table.toNat + 81 * capacity.toNat + 114 ≤ 33806089496)
    (positive : 0 < capacity.toNat)
    (tableDomain : ∀ address : BitVec 64, table.toNat ≤ address.toNat →
      address.toNat < (htabNewOrderPos table keyLength capacity).toNat + capacity.toNat * 8 → state.memaddrs address)
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
      ready.memory (table + 0) = .word keyLength ∧
      ready.memory (table + 8) = .word (allocationEnd 0 keyLength) ∧
      ready.memory (table + 16) = .word capacity ∧
      ready.memory (table + 24) = .word 0 ∧
      ready.memory (table + 32) = .word (allocationEnd table 72) ∧
      ready.memory (table + 40) = .word (htabNewValues table keyLength capacity) ∧
      ready.memory (table + 48) = .word (htabNewUsed table keyLength capacity) ∧
      ready.memory (table + 56) = .word (htabNewOrder table keyLength capacity) ∧
      ready.memory (table + 64) = .word (htabNewOrderPos table keyLength capacity) ∧
      HashInsertTableMemory capacity (htabNewUsed table keyLength capacity) table
        (htabNewValues table keyLength capacity) (htabNewOrder table keyLength capacity)
        (htabNewOrderPos table keyLength capacity) 0 ready ∧
      ∀ name continuation,
        evaluateHOLFiniteState state (.decCall name .one (ofString "htab_new") [keyArgument,capacityArgument] continuation) =
          (let output := evaluateHOLFiniteState (setVarHOLFinite name (.val (.word table)) ready) continuation;
           (output.1,{output.2 with locals := (HolFiniteMapExact.resVarEq output.2.locals
             (name,state.locals.lookup name))})) := by
  obtain ⟨ready,run,empty,cost,remaining,locals,postCode,addresses,endian,
      keyField,strideField,capField,countField,keysField,valuesField,usedField,orderField,reverseField,decl⟩ :=
    evaluate_htabNew_header_call_and_declaration state keyArgument capacityArgument table keyLength capacity
      arguments code ticks heap keyBound tableAligned budget headerDomain wordDomain byteDomain
  have domainAfter : ∀ address : BitVec 64, table.toNat ≤ address.toNat →
      address.toNat < (htabNewOrderPos table keyLength capacity).toNat + capacity.toNat * 8 → ready.memaddrs address := by
    rw [addresses]
    exact tableDomain
  have facts := htabNew_insertion_memory ready table keyLength capacity 0 keyBound budget domainAfter
    valuesField countField (by change 0 = _; exact empty.symm) positive
  exact ⟨ready,run,empty,cost,remaining,locals,postCode,addresses,endian,
    keyField,strideField,capField,countField,keysField,valuesField,usedField,orderField,reverseField,facts,decl⟩

#print axioms evaluate_htabNew_insertion_call_and_declaration
end InitECandidate.Runtime
