import InitECandidate.Runtime.HashNewOrderHeap
import InitECandidate.Runtime.HashTableReadyAdvanceFrame
import InitECandidate.Runtime.HashTableReadyWordOutside
import InitECandidate.Runtime.AllocationPlanFacts
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- Final order allocations and pointer stores preserve an earlier table. -/
theorem evaluate_htabNew_order_tail_other_width {F : Type} (state : PanSemStateFiniteExact 64 F)
    (pointer table capacity : BitVec 64)
    (code : state.code = originalRuntimeCode) (clock : 2 ≤ state.clock)
    (heapGlobal : state.globals.lookup (ofString "heap_ptr") = some (.val (.word pointer)))
    (safe : AllocationPlanSafe pointer [capacity * 8,capacity * 8])
    (tableLocal : state.locals.lookup (ofString "t") = some (.val (.word table)))
    (capLocal : state.locals.lookup (ofString "cap") = some (.val (.word capacity)))
    (domain56 : state.memaddrs (table + 56)) (domain64 : state.memaddrs (table + 64))
    (oldKeyLength otherTable keys stride otherCapacity used values order orderPos items : BitVec 64) (bits : Nat)
    (ready : HashTableReady oldKeyLength otherTable keys stride otherCapacity used values order orderPos items bits pointer state)
    (outside56 : (table + 56).toNat < otherTable.toNat ∨ orderPos.toNat + otherCapacity.toNat * 8 ≤ (table + 56).toNat)
    (outside64 : (table + 64).toNat < otherTable.toNat ∨ orderPos.toNat + otherCapacity.toNat * 8 ≤ (table + 64).toNat) :
    ∃ post, evaluateHOLFiniteState state htabNewAfterZero = (some (.returned (.val (.word table))),post) ∧
      HashTableReady oldKeyLength otherTable keys stride otherCapacity used values order orderPos items bits
        (allocationEnd (allocationEnd pointer (capacity * 8)) (capacity * 8)) post ∧
      post.clock = state.clock - 2 ∧ post.code = state.code ∧ post.memaddrs = state.memaddrs ∧ post.be = state.be := by
  obtain ⟨post,run,ticks,postCode,domain,endian,heap,memory⟩ :=
    evaluate_htabNew_order_tail_heap state pointer table capacity code clock heapGlobal safe tableLocal capLocal domain56 domain64
  have first := ready.after_word_outside state oldKeyLength otherTable pointer keys stride otherCapacity used values order orderPos items (table + 56) pointer bits outside56
  have second := first.after_word_outside _ oldKeyLength otherTable pointer keys stride otherCapacity used values order orderPos items (table + 64) (allocationEnd pointer (capacity * 8)) bits outside64
  have facts := allocationPlan_facts [capacity * 8,capacity * 8] pointer safe ready.live.frontier.bounded ready.live.frontier.aligned
  simp only [allocationPlanEnd] at facts
  have frame : ∀ address : BitVec 64, otherTable.toNat ≤ address.toNat → address.toNat < orderPos.toNat + otherCapacity.toNat * 8 → post.memory address = state.memory address := by
    intro address lower upper
    have neq56 : address ≠ table + 56 := by
      intro same
      have equal := congrArg BitVec.toNat same
      rcases outside56 with before | after <;> omega
    have neq64 : address ≠ table + 64 := by
      intro same
      have equal := congrArg BitVec.toNat same
      rcases outside64 with before | after <;> omega
    rw [memory]
    simp only [sourceWriteWord,if_neg neq64,if_neg neq56]
  have retained := ready.interval_frame_advance state post oldKeyLength otherTable pointer
    (allocationEnd (allocationEnd pointer (capacity * 8)) (capacity * 8)) keys stride otherCapacity used values order orderPos items bits
    frame heap (by omega) facts.2.1 facts.2.2 postCode domain endian
  exact ⟨post,run,retained,ticks,postCode,domain,endian⟩

#print axioms evaluate_htabNew_order_tail_other_width
end InitECandidate.Runtime
