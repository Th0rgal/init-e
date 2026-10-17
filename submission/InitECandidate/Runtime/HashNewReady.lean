import InitECandidate.Runtime.HashNewArraysInvariant
import InitECandidate.Runtime.HashNewHeaderCallHeap
import InitECandidate.Runtime.HashNewEntryInvariants32
import InitECandidate.Runtime.HashTableReady
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- Constructor establishes every mixed-operation fact for its actual key width. -/
theorem evaluate_htabNew_ready {F : Type} (state : PanSemStateFiniteExact 64 F)
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
    evaluate_htabNew_arrays_invariant state keyArgument capacityArgument table keyLength capacity bits arguments power tableDomain code ticks heap
      keyBound tableAligned budget headerDomain wordDomain byteDomain
  obtain ⟨checked,checkedRun,_,_,_,_,_,_,_,heapAfter,_⟩ :=
    evaluate_htabNew_header_call_and_declaration_heap state keyArgument capacityArgument table keyLength capacity arguments code ticks heap
      keyBound tableAligned budget headerDomain wordDomain byteDomain
  have same : ready = checked := congrArg Prod.snd (run.symm.trans checkedRun)
  have finalHeap : ready.globals.lookup (ofString "heap_ptr") = some (.val (.word (allocationEnd (htabNewOrderPos table keyLength capacity) (capacity * 8)))) := by
    rw [same]
    exact heapAfter
  have frontier := htabNew_frontier_facts table keyLength capacity keyBound budget
  have entries := hashEmpty_entry_invariants ready (htabNewUsed table keyLength capacity) (htabNewValues table keyLength capacity)
    (htabNewOrderPos table keyLength capacity) capacity empty
  exact ⟨ready,run,empty,cost,remaining,locals,postCode,domain,endian,
    ⟨⟨arrays,HashOrderEntriesBound.empty _ _ _,⟨finalHeap,frontier.1,frontier.2.1,frontier.2.2⟩⟩,
      entries.1,entries.2,HashOrderLinked.empty ready (htabNewUsed table keyLength capacity) (htabNewOrder table keyLength capacity)
        (htabNewOrderPos table keyLength capacity) capacity empty,htabNew_keys_before_values table keyLength capacity keyBound budget⟩,decl⟩

#print axioms evaluate_htabNew_ready
end InitECandidate.Runtime
