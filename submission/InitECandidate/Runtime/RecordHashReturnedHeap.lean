import InitECandidate.Runtime.RecordHashBodyBound
import InitECandidate.Runtime.MerkleMarkedHeap
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

theorem recordHash_suffix_marked (steps : List RecordHashStep) (count : BitVec 64) :
    MarkedHeapReturn (ofString "mark") (recordHashSuffix steps count) := by
  induction steps with
  | nil =>
    apply MarkedHeapReturn.seq _ rfl rfl
    exact MarkedHeapReturn.finish
  | cons step rest ih =>
    exact MarkedHeapReturn.seq _ rfl rfl ih

theorem recordHash_allocation_marked (steps : List RecordHashStep) (count : BitVec 64) :
    MarkedHeapReturn (ofString "mark") (recordHashAllocation count steps) :=
  MarkedHeapReturn.decCall _ _ _ _ (by decide) (recordHash_suffix_marked steps count)

/-- Every returned fixed-record hash restores its original heap frontier,
without clock, input-readability, or successful-allocation assumptions. -/
theorem recordHash_body_returned_heap {F : Type} (state post : PanSemStateFiniteExact 64 F)
    (count heap : BitVec 64) (steps : List RecordHashStep) (value : ValueHOL 64)
    (code : state.code = originalRuntimeCode)
    (atHeap : state.globals.lookup (ofString "heap_ptr") = some (.val (.word heap)))
    (run : evaluateHOLFiniteState state (recordHashBody count steps) = (some (.returned value),post)) :
    post.globals.lookup (ofString "heap_ptr") = some (.val (.word heap)) := by
  change evaluateHOLFiniteState state
    (.decCall (ofString "mark") .one (ofString "heap_mark") [] (recordHashAllocation count steps)) = _ at run
  have ticks := evaluate_decCall_returned_nonzero_clock state post (ofString "mark") (ofString "heap_mark")
    .one [] (recordHashAllocation count steps) value run
  obtain ⟨ready,_,_,_,_,_,installed,_,_,declaration⟩ :=
    evaluate_heapMark_call_and_declaration state heap code atHeap ticks
  rw [declaration (ofString "mark") (recordHashAllocation count steps)] at run
  cases bodyRun : evaluateHOLFiniteState (setVarHOLFinite (ofString "mark") (.val (.word heap)) ready)
      (recordHashAllocation count steps) with
  | mk result output =>
    rw [bodyRun] at run
    have resultEq := (Prod.mk.inj run).1
    dsimp only at resultEq
    subst result
    have restored := (recordHash_allocation_marked steps count).returned
      (setVarHOLFinite (ofString "mark") (.val (.word heap)) ready) output heap value (installed.trans code)
      (by simp [setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]) bodyRun
    have globals : post.globals = output.globals := by rw [← (Prod.mk.inj run).2]
    rw [globals]
    exact restored

#print axioms recordHash_suffix_marked
#print axioms recordHash_allocation_marked
#print axioms recordHash_body_returned_heap
end InitECandidate.Runtime
