import InitECandidate.Runtime.HtrPayloadSource
import InitECandidate.Runtime.HtrPcontainerCallBound
import InitECandidate.Runtime.HtrU64AtBound
import InitECandidate.Runtime.RunBoundedDiscardHeap
import InitECandidate.Runtime.VmFn_heap_release
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
set_option maxRecDepth 100000

theorem source_htrPayload_container : htrPayloadAt 35 =
    .seq (.call (some (none,none)) (ofString "htr_pcontainer")
      [.var .local (ofString "ch"),.const 19,.var .local (ofString "out")])
      (htrPayloadAt 36) := by rfl

theorem source_htrPayload_finish : htrPayloadAt 36 =
    .seq (.call (some (none,none)) (ofString "heap_release") [.var .local (ofString "mark")])
      (.return (.const 0)) := by rfl

theorem source_htrPayload_last_u64 : htrPayloadAt 34 =
    .seq (.call (some (none,none)) (ofString "htr_u64_at")
      [.op .add [.var .local (ofString "raw"),.const 532],
       .op .add [.var .local (ofString "ch"),.const 576]]) (htrPayloadAt 35) := by rfl

def htrPayloadContainerSuffixCost : Nat := (htrPcontainerBodyCost + 1) + 1

theorem runBounded_htrPayload_container_suffix {F : Type} (state : PanSemStateFiniteExact 64 F)
    (chunks out heap : BitVec 64)
    (chunksLocal : state.locals.lookup (ofString "ch") = some (.val (.word chunks)))
    (outLocal : state.locals.lookup (ofString "out") = some (.val (.word out)))
    (heapGlobal : state.globals.lookup (ofString "heap_ptr") = some (.val (.word heap)))
    (heapBound : heap.toNat ≤ 33806089496) (code : state.code = originalRuntimeCode)
    (budget : htrPayloadContainerSuffixCost ≤ state.clock) :
    RunBounded state (htrPayloadAt 35) htrPayloadContainerSuffixCost := by
  rw [source_htrPayload_container]
  have args : evalListHOLFinite state (h := fun a => Classical.propDecidable (state.memaddrs a))
      [.var .local (ofString "ch"),.const 19,.var .local (ofString "out")] =
      some [.val (.word chunks),.val (.word (19#64)),.val (.word out)] := by
    simp [evalListHOLExact,evalHOLExact,chunksLocal,outLocal]
  exact RunBounded.seq (runBounded_htrPcontainer_call state none _ chunks 19 out heap args (by decide)
    heapGlobal heapBound code (by unfold htrPayloadContainerSuffixCost at budget; omega)) budget (by
      intro next normal nextCode remaining
      rw [source_htrPayload_finish]
      exact RunBounded.ofProg
        (ProgBounded.seq (ProgBounded.call vmBound_heap_release _ _) (ProgBounded.straight _ (by decide)))
        (nextCode.trans code) remaining)

def htrPayloadFinalSuffixCost : Nat := 30 + htrPayloadContainerSuffixCost

theorem runBounded_htrPayload_final_suffix {F : Type} (state : PanSemStateFiniteExact 64 F)
    (chunks out heap : BitVec 64)
    (chunksLocal : state.locals.lookup (ofString "ch") = some (.val (.word chunks)))
    (outLocal : state.locals.lookup (ofString "out") = some (.val (.word out)))
    (heapGlobal : state.globals.lookup (ofString "heap_ptr") = some (.val (.word heap)))
    (heapBound : heap.toNat ≤ 33806089496) (code : state.code = originalRuntimeCode)
    (budget : htrPayloadFinalSuffixCost ≤ state.clock) :
    RunBounded state (htrPayloadAt 34) htrPayloadFinalSuffixCost := by
  rw [source_htrPayload_last_u64]
  apply runBounded_discard_heap_seq state (ofString "htr_u64_at") _ _ (ofString "heap_ptr") heap
    30 htrPayloadContainerSuffixCost
    (RunBounded.ofProg (ProgBounded.call htrU64At_funBounded _ _) code (by unfold htrPayloadFinalSuffixCost at budget; omega)) budget
  · intro next normal
    have globals := htrU64At_call_globals
      [.op .add [.var .local (ofString "raw"),.const 532],
       .op .add [.var .local (ofString "ch"),.const 576]] state code
    rw [normal] at globals
    rw [globals]
    exact heapGlobal
  · intro next keep heapKept nextCode remaining
    exact runBounded_htrPayload_container_suffix next chunks out heap
      ((keep _).trans chunksLocal) ((keep _).trans outLocal) heapKept heapBound (nextCode.trans code) remaining

#print axioms source_htrPayload_container
#print axioms source_htrPayload_finish
#print axioms source_htrPayload_last_u64
#print axioms runBounded_htrPayload_container_suffix
#print axioms runBounded_htrPayload_final_suffix
end InitECandidate.Runtime
