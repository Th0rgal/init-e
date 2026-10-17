import InitECandidate.Runtime.AllocationPointerStore
import InitECandidate.Runtime.HashTableReadyAdvanceFrame
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- Array allocation and its pointer store preserve an earlier ready table. -/
theorem HashTableReady.allocation_pointer_store {F : Type} (state : PanSemStateFiniteExact 64 F)
    (name tableName : MlS) (argument : ExpHOL 64) (pointer size table offset : BitVec 64)
    (continuation : ProgHOL 64) (different : name ≠ tableName)
    (arguments : evalListHOLFinite state
      (h := fun address => Classical.propDecidable (state.memaddrs address)) [argument] = some [.val (.word size)])
    (code : state.code = originalRuntimeCode) (clock : state.clock ≠ 0)
    (heapGlobal : state.globals.lookup (ofString "heap_ptr") = some (.val (.word pointer)))
    (request : size ≤ (33806089496 : BitVec 64) - pointer)
    (finishBound : (allocationEnd pointer size).toNat ≤ 33806089496)
    (tableLocal : state.locals.lookup tableName = some (.val (.word table)))
    (domain : state.memaddrs (table + offset))
    (keyLength otherTable keys stride capacity used values order orderPos items : BitVec 64) (bits : Nat)
    (valid : HashTableReady keyLength otherTable keys stride capacity used values order orderPos items bits pointer state)
    (outside : (table + offset).toNat < otherTable.toNat ∨ orderPos.toNat + capacity.toNat * 8 ≤ (table + offset).toNat) :
    ∃ ready, evaluateHOLFiniteState state
        (.decCall name .one (ofString "alloc") [argument]
          (.seq (.store (hashLocalAddress tableName offset) (.var .local name)) continuation)) =
        (let output := evaluateHOLFiniteState ready continuation;
          (output.1,{output.2 with locals := (HolFiniteMapExact.resVarEq output.2.locals
            (name,state.locals.lookup name))})) ∧
      HashTableReady keyLength otherTable keys stride capacity used values order orderPos items bits (allocationEnd pointer size) ready ∧
      ready.clock = state.clock - 1 ∧
      ready.locals = (setVarHOLFinite name (.val (.word pointer)) state).locals ∧
      ready.memory = (sourceWriteWord state (table + offset) pointer).memory ∧
      ready.memory (table + offset) = .word pointer ∧
      ready.globals.lookup (ofString "heap_ptr") = some (.val (.word (allocationEnd pointer size))) ∧
      ready.code = state.code ∧ ready.memaddrs = state.memaddrs ∧ ready.be = state.be := by
  obtain ⟨ready,run,ticks,locals,memory,cell,heap,postCode,addresses,endian⟩ :=
    evaluate_allocation_pointer_store state name tableName argument pointer size table offset continuation different arguments code clock heapGlobal request finishBound tableLocal domain
  have small := allocationGuard_sum_bound pointer size valid.live.frontier.bounded request
  have cover := allocationEnd_covers pointer size small
  have frame : ∀ address : BitVec 64, otherTable.toNat ≤ address.toNat → address.toNat < orderPos.toNat + capacity.toNat * 8 → ready.memory address = state.memory address := by
    intro address lower upper
    have neq : address ≠ table + offset := by
      intro same
      have equal := congrArg BitVec.toNat same
      rcases outside with before | after <;> omega
    rw [memory]
    simp only [sourceWriteWord,if_neg neq]
  have preserved := valid.interval_frame_advance state ready keyLength otherTable pointer (allocationEnd pointer size) keys stride capacity used values order orderPos items bits
    frame heap (by omega) finishBound cover.2.2 postCode addresses endian
  exact ⟨ready,run,preserved,ticks,locals,memory,cell,heap,postCode,addresses,endian⟩

#print axioms HashTableReady.allocation_pointer_store
end InitECandidate.Runtime
