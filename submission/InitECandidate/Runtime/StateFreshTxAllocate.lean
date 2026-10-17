import InitECandidate.Runtime.AllocationGlobalCall
import InitECandidate.Runtime.HashInsertCountTail
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- Allocate the concrete transaction-state header and store its block-state parent. -/
theorem evaluate_stateFreshTx_allocate {F : Type} (state : PanSemStateFiniteExact 64 F)
    (pointer oldTs bs : BitVec 64) (code : state.code = originalRuntimeCode) (clock : state.clock ≠ 0)
    (heap : state.globals.lookup (ofString "heap_ptr") = some (.val (.word pointer)))
    (tsGlobal : state.globals.lookup (ofString "ts") = some (.val (.word oldTs)))
    (bsGlobal : state.globals.lookup (ofString "bs") = some (.val (.word bs)))
    (request : (72 : BitVec 64) ≤ (33806089496 : BitVec 64) - pointer)
    (finish : (allocationEnd pointer 72).toNat ≤ 33806089496) (domain : state.memaddrs pointer) :
    ∃ ready, evaluateHOLFiniteState state
      (.seq (.call (some (some (.global,ofString "ts"),none)) (ofString "alloc") [.const 72])
        (.store (.op .add [.var .global (ofString "ts"),.const 0]) (.var .global (ofString "bs")))) = (none,ready) ∧
      ready.clock = state.clock - 1 ∧ ready.locals = state.locals ∧ ready.code = state.code ∧
      ready.memaddrs = state.memaddrs ∧ ready.be = state.be ∧ ready.memory pointer = .word bs ∧
      ready.globals.lookup (ofString "ts") = some (.val (.word pointer)) ∧
      ready.globals.lookup (ofString "heap_ptr") = some (.val (.word (allocationEnd pointer 72))) ∧
      (∀ watched, watched ≠ ofString "ts" → watched ≠ ofString "heap_ptr" → ready.globals.lookup watched = state.globals.lookup watched) := by
  obtain ⟨allocated,run,ticks,_,locals,postCode,addresses,endian,ts,heapNext,globals⟩ :=
    evaluate_alloc_global_call state (.const 72) pointer 72 oldTs (ofString "ts") rfl code clock heap tsGlobal (by decide) request finish
  have bsAfter : allocated.globals.lookup (ofString "bs") = some (.val (.word bs)) :=
    (globals (ofString "bs") (by decide) (by decide)).trans bsGlobal
  have store := evaluate_store_word allocated pointer bs
    (.op .add [.var .global (ofString "ts"),.const 0]) (.var .global (ofString "bs"))
    (by simp [evalHOLExact,evalListHOLExact,ts,wordOpHOL,wordOp,valueIsWord,valueWord]) bsAfter
    (by rw [addresses]; exact domain)
  refine ⟨sourceWriteWord allocated pointer bs,?_,ticks,locals,postCode,addresses,endian,?_,ts,heapNext,globals⟩
  · rw [evaluateHOLFiniteState_seq_line780,run]
    exact store
  · simp [sourceWriteWord]

#print axioms evaluate_stateFreshTx_allocate
end InitECandidate.Runtime
