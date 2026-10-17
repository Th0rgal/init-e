import InitECandidate.Runtime.HashNewHeaderCall
import InitECandidate.Runtime.HashNewKeyLayout
import InitECandidate.Runtime.HashNewLayout
import InitECandidate.Runtime.HashTableArraysInvariant
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- The actual constructor establishes relocated geometry for its requested key width. -/
theorem evaluate_htabNew_arrays_invariant {F : Type} (state : PanSemStateFiniteExact 64 F)
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
    (budget : table.toNat + 81 * capacity.toNat + 114 ≤ 33806089496)
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
    evaluate_htabNew_header_call_and_declaration state keyArgument capacityArgument table keyLength capacity
      arguments code ticks heap keyBound tableAligned budget headerDomain wordDomain byteDomain
  refine ⟨ready,run,empty,cost,remaining,locals,postCode,addresses,endian,?_,decl⟩
  obtain ⟨va,ua,oa,ra,hv,vu,uo,orr,limit⟩ := htabNew_insertion_layout table keyLength capacity keyBound budget
  obtain ⟨ka,sa,fits,hk,ku⟩ := htabNew_key_layout table keyLength capacity keyBound budget
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

#print axioms evaluate_htabNew_arrays_invariant
end InitECandidate.Runtime
