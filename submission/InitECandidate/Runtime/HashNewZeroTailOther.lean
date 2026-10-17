import InitECandidate.Runtime.HashNewZeroOther
import InitECandidate.Runtime.HashNewOrderOther
import InitECandidate.Runtime.HashNewZeroHeap
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- Occupancy initialization and final constructor allocations preserve an earlier table. -/
theorem evaluate_htabNew_zero_tail_other_width {F : Type} (state : PanSemStateFiniteExact 64 F)
    (pointer table keyLength capacity : BitVec 64)
    (code : state.code = originalRuntimeCode) (ticks : capacity.toNat + 3 ≤ state.clock)
    (heap : state.globals.lookup (ofString "heap_ptr") = some (.val (.word pointer)))
    (safe : AllocationPlanSafe pointer [capacity * 8,capacity * 8])
    (keyBound : keyLength.toNat ≤ 52) (tableAligned : table.toNat % 8 = 0)
    (budget : table.toNat + 81 * capacity.toNat + 114 ≤ 33806089496)
    (tableLocal : state.locals.lookup (ofString "t") = some (.val (.word table)))
    (usedLocal : state.locals.lookup (ofString "used") = some (.val (.word (htabNewUsed table keyLength capacity))))
    (capLocal : state.locals.lookup (ofString "cap") = some (.val (.word capacity)))
    (domain48 : state.memaddrs (table + 48)) (domain56 : state.memaddrs (table + 56))
    (domain64 : state.memaddrs (table + 64))
    (wordDomain : ∀ offset : Nat, offset < capacity.toNat →
      state.memaddrs (htabNewUsed table keyLength capacity + BitVec.ofNat 64 offset))
    (byteDomain : ∀ offset : Nat, offset < capacity.toNat →
      state.memaddrs (panByteAlignHOL (htabNewUsed table keyLength capacity + BitVec.ofNat 64 offset)))
    (oldKeyLength otherTable keys stride otherCapacity used values order orderPos items : BitVec 64) (bits : Nat)
    (otherReady : HashTableReady oldKeyLength otherTable keys stride otherCapacity used values order orderPos items bits pointer state)
    (outside : (htabNewUsed table keyLength capacity).toNat + capacity.toNat ≤ otherTable.toNat ∨ orderPos.toNat + otherCapacity.toNat * 8 ≤ (htabNewUsed table keyLength capacity).toNat)
    (outside48 : (table + 48).toNat < otherTable.toNat ∨ orderPos.toNat + otherCapacity.toNat * 8 ≤ (table + 48).toNat)
    (outside56 : (table + 56).toNat < otherTable.toNat ∨ orderPos.toNat + otherCapacity.toNat * 8 ≤ (table + 56).toNat)
    (outside64 : (table + 64).toNat < otherTable.toNat ∨ orderPos.toNat + otherCapacity.toNat * 8 ≤ (table + 64).toNat) :
    ∃ post, evaluateHOLFiniteState state htabNewUsedBody = (some (.returned (.val (.word table))),post) ∧
      HashTableReady oldKeyLength otherTable keys stride otherCapacity used values order orderPos items bits
        (allocationEnd (allocationEnd pointer (capacity * 8)) (capacity * 8)) post ∧
      hashOccupiedCount capacity (hashOccupancyRead post (htabNewUsed table keyLength capacity)) = 0 ∧
      state.clock ≤ post.clock + capacity.toNat + 3 ∧ post.clock ≤ state.clock ∧
      post.code = state.code ∧ post.memaddrs = state.memaddrs ∧ post.be = state.be := by
  obtain ⟨ready,run,preserved,_,_,cost,remaining,locals,globals,postCode,domain,endian⟩ :=
    evaluate_htabNew_zero_prefix_other_width state table keyLength capacity htabNewAfterZero code (by omega)
      keyBound tableAligned budget tableLocal usedLocal capLocal domain48 wordDomain byteDomain
      oldKeyLength otherTable pointer keys stride otherCapacity used values order orderPos items bits otherReady outside outside48
  obtain ⟨post,tail,postReady,clock,lastCode,lastDomain,lastEndian⟩ :=
    evaluate_htabNew_order_tail_other_width ready pointer table capacity (postCode.trans code) (by omega)
      (by rw [globals]; exact heap) safe (by rw [locals]; exact tableLocal) (by rw [locals]; exact capLocal)
      (by rw [domain]; exact domain56) (by rw [domain]; exact domain64)
      oldKeyLength otherTable keys stride otherCapacity used values order orderPos items bits preserved outside56 outside64
  have actual : evaluateHOLFiniteState state htabNewUsedBody = (some (.returned (.val (.word table))),post) := by
    rw [source_htabNew_zero_prefix,run,tail]
  obtain ⟨checked,checkedRun,empty,_,_,_,_,_,_⟩ := evaluate_htabNew_zero_tail_heap state pointer table keyLength capacity code ticks heap safe
    keyBound tableAligned budget tableLocal usedLocal capLocal domain48 domain56 domain64 wordDomain byteDomain
  have same : post = checked := congrArg Prod.snd (actual.symm.trans checkedRun)
  exact ⟨post,actual,postReady,by rw [same]; exact empty,by omega,by omega,lastCode.trans postCode,lastDomain.trans domain,lastEndian.trans endian⟩

#print axioms evaluate_htabNew_zero_tail_other_width
end InitECandidate.Runtime
