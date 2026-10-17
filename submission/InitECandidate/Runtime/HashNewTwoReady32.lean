import InitECandidate.Runtime.HashNewReady32
import InitECandidate.Runtime.HashNewCallOther32
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- One constructor call creates a ready table and retains the earlier ready table. -/
theorem evaluate_htabNew_two_ready32 {F : Type} (state : PanSemStateFiniteExact 64 F)
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
      state.memaddrs (panByteAlignHOL (htabNewUsed table (32 : BitVec 64) capacity + BitVec.ofNat 64 offset)))    (otherTable keys otherStride otherCapacity used values order orderPos items : BitVec 64) (otherBits : Nat)
    (otherReady : HashTableReady32 otherTable keys otherStride otherCapacity used values order orderPos items otherBits table state)
    (earlier : orderPos.toNat + otherCapacity.toNat * 8 ≤ table.toNat) :
    ∃ ready, evaluateHOLFiniteState state
        (.call (some (none,none)) (ofString "htab_new") [keyArgument,capacityArgument]) = (none,ready) ∧
      HashTableReady32 table (allocationEnd table 72) (allocationEnd 0 32) capacity
        (htabNewUsed table 32 capacity) (htabNewValues table 32 capacity) (htabNewOrder table 32 capacity)
        (htabNewOrderPos table 32 capacity) 0 bits
        (allocationEnd (htabNewOrderPos table 32 capacity) (capacity * 8)) ready ∧
      HashTableReady32 otherTable keys otherStride otherCapacity used values order orderPos items otherBits (allocationEnd (htabNewOrderPos table 32 capacity) (capacity * 8)) ready ∧
      state.clock ≤ ready.clock + capacity.toNat + 8 ∧ ready.clock ≤ state.clock ∧
      ready.locals = state.locals ∧ ready.code = state.code ∧ ready.memaddrs = state.memaddrs ∧ ready.be = state.be ∧
      (∀ name continuation,
        evaluateHOLFiniteState state (.decCall name .one (ofString "htab_new") [keyArgument,capacityArgument] continuation) =
          (let output := evaluateHOLFiniteState (setVarHOLFinite name (.val (.word table)) ready) continuation;
           (output.1,{output.2 with locals := HolFiniteMapExact.resVarEq output.2.locals (name,state.locals.lookup name)}))) := by
  obtain ⟨ready,run,newReady,cost,remaining,locals,postCode,domain,endian,decl⟩ :=
    evaluate_htabNew_ready32 state keyArgument capacityArgument table capacity bits arguments power tableDomain code ticks heap
      keyBound tableAligned budget headerDomain wordDomain byteDomain
  obtain ⟨checked,checkedRun,preserved,_,_,_,_,_,_,_,_⟩ :=
    evaluate_htabNew_call_with_other state keyArgument capacityArgument table 32 capacity arguments code ticks heap
      keyBound tableAligned budget headerDomain wordDomain byteDomain
      otherTable keys otherStride otherCapacity used values order orderPos items otherBits otherReady earlier
  have same : ready = checked := congrArg Prod.snd (run.symm.trans checkedRun)
  have oldReady : HashTableReady32 otherTable keys otherStride otherCapacity used values order orderPos items otherBits
      (allocationEnd (htabNewOrderPos table 32 capacity) (capacity * 8)) ready := by
    rw [same]
    exact preserved
  exact ⟨ready,run,newReady,oldReady,cost,remaining,locals,postCode,domain,endian,decl⟩

#print axioms evaluate_htabNew_two_ready32
end InitECandidate.Runtime
