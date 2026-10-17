import InitECandidate.Runtime.HashNewReady
import InitECandidate.Runtime.HashNewCallOther
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- One constructor output establishes the requested table and retains all existing mixed-width tables. -/
theorem evaluate_htabNew_ready_frame {F : Type} (state : PanSemStateFiniteExact 64 F)
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
      (∀ (oldKeyLength oldTable oldKeys oldStride oldCapacity oldUsed oldValues oldOrder oldOrderPos oldItems : BitVec 64) (oldBits : Nat),
        HashTableReady oldKeyLength oldTable oldKeys oldStride oldCapacity oldUsed oldValues oldOrder oldOrderPos oldItems oldBits table state →
        HashTableReady oldKeyLength oldTable oldKeys oldStride oldCapacity oldUsed oldValues oldOrder oldOrderPos oldItems oldBits
          (allocationEnd (htabNewOrderPos table keyLength capacity) (capacity * 8)) ready) ∧
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
  obtain ⟨ready,run,empty,cost,remaining,locals,postCode,domain,endian,newReady,decl⟩ :=
    evaluate_htabNew_ready state keyArgument capacityArgument table keyLength capacity bits arguments power tableDomain code ticks heap
      keyBound tableAligned budget headerDomain wordDomain byteDomain
  refine ⟨ready,run,empty,?_,cost,remaining,locals,postCode,domain,endian,newReady,decl⟩
  intro oldKeyLength oldTable oldKeys oldStride oldCapacity oldUsed oldValues oldOrder oldOrderPos oldItems oldBits oldReady
  obtain ⟨checked,checkedRun,preserved,_,_,_,_,_,_,_,_⟩ :=
    evaluate_htabNew_call_with_other_width state keyArgument capacityArgument table keyLength capacity arguments code ticks heap
      keyBound tableAligned budget headerDomain wordDomain byteDomain
      oldKeyLength oldTable oldKeys oldStride oldCapacity oldUsed oldValues oldOrder oldOrderPos oldItems oldBits oldReady oldReady.live.frontier.allocated
  have same : ready = checked := congrArg Prod.snd (run.symm.trans checkedRun)
  rw [same]
  exact preserved

#print axioms evaluate_htabNew_ready_frame
end InitECandidate.Runtime
