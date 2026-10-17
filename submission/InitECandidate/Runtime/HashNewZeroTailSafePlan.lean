import InitECandidate.Runtime.HashNewZeroSafePlan
import InitECandidate.Runtime.HashNewOrderTail
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- Occupancy clearing and the two remaining arrays retain the empty-table
invariant under the actual safe plan, including plans near the heap limit. -/
theorem evaluate_htabNew_zero_tail_of_safe_plan {F : Type} (state : PanSemStateFiniteExact 64 F)
    (pointer table keyLength capacity : BitVec 64)
    (code : state.code = originalRuntimeCode) (ticks : capacity.toNat + 3 ≤ state.clock)
    (heap : state.globals.lookup (ofString "heap_ptr") = some (.val (.word pointer)))
    (safe : AllocationPlanSafe pointer [capacity * 8,capacity * 8])
    (pointerBound : table.toNat ≤ 33806089496) (tableAligned : table.toNat % 8 = 0)
    (fullSafe : AllocationPlanSafe table (htabNewAllocationSizes keyLength capacity))
    (tableLocal : state.locals.lookup (ofString "t") = some (.val (.word table)))
    (usedLocal : state.locals.lookup (ofString "used") = some (.val (.word (htabNewUsed table keyLength capacity))))
    (capLocal : state.locals.lookup (ofString "cap") = some (.val (.word capacity)))
    (domain48 : state.memaddrs (table + 48)) (domain56 : state.memaddrs (table + 56))
    (domain64 : state.memaddrs (table + 64))
    (wordDomain : ∀ offset : Nat, offset < capacity.toNat →
      state.memaddrs (htabNewUsed table keyLength capacity + BitVec.ofNat 64 offset))
    (byteDomain : ∀ offset : Nat, offset < capacity.toNat →
      state.memaddrs (panByteAlignHOL (htabNewUsed table keyLength capacity + BitVec.ofNat 64 offset))) :
    ∃ post, evaluateHOLFiniteState state htabNewUsedBody = (some (.returned (.val (.word table))),post) ∧
      hashOccupiedCount capacity (hashOccupancyRead post (htabNewUsed table keyLength capacity)) = 0 ∧
      state.clock ≤ post.clock + capacity.toNat + 3 ∧ post.clock ≤ state.clock ∧
      post.code = state.code ∧ post.memaddrs = state.memaddrs ∧ post.be = state.be := by
  obtain ⟨ready,run,empty,_,cost,remaining,locals,globals,postCode,addresses,endian⟩ :=
    evaluate_htabNew_zero_prefix_of_safe_plan state table keyLength capacity htabNewAfterZero code (by omega)
      pointerBound tableAligned fullSafe tableLocal usedLocal capLocal domain48 wordDomain byteDomain
  obtain ⟨post,tail,clock,lastCode,lastAddresses,lastEndian,counts⟩ :=
    evaluate_htabNew_order_tail ready pointer table capacity (postCode.trans code) (by omega)
      (by rw [globals]; exact heap) safe (by rw [locals]; exact tableLocal) (by rw [locals]; exact capLocal)
      (by rw [addresses]; exact domain56) (by rw [addresses]; exact domain64)
  refine ⟨post,?_,?_,by omega,by omega,lastCode.trans postCode,lastAddresses.trans addresses,lastEndian.trans endian⟩
  · rw [source_htabNew_zero_prefix,run,tail]
  · rw [counts]
    · exact empty
    · intro index inside
      exact ⟨htabNew_header_separate_of_safe_plan table keyLength capacity pointerBound tableAligned fullSafe 56 (by decide) index inside,
        htabNew_header_separate_of_safe_plan table keyLength capacity pointerBound tableAligned fullSafe 64 (by decide) index inside⟩

#print axioms evaluate_htabNew_zero_tail_of_safe_plan
end InitECandidate.Runtime
