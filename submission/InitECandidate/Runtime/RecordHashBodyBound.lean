import InitECandidate.Runtime.RecordHashSuffixBound
import InitECandidate.Runtime.AllocationDeclarationReach
import InitECandidate.Runtime.HeapMarkDeclarationReach
import InitECandidate.Runtime.ReachesTerminalBound
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

def recordHashAllocation (count : BitVec 64) (steps : List RecordHashStep) : ProgHOL 64 :=
  .decCall (ofString "ch") .one (ofString "alloc") [.panop .mul [.const count,.const 32]] (recordHashSuffix steps count)

theorem recordHash_allocation_bound {F : Type} (state : PanSemStateFiniteExact 64 F)
    (count e out heap : BitVec 64) (steps : List RecordHashStep)
    (atInput : state.locals.lookup (ofString "e") = some (.val (.word e)))
    (atOut : state.locals.lookup (ofString "out") = some (.val (.word out)))
    (hh : state.globals.lookup (ofString "heap_ptr") = some (.val (.word heap)))
    (cap : heap.toNat ≤ 33806089496) (small : ∀ step ∈ steps, step.Small)
    (countBound : count.toNat ≤ 134217712) (code : state.code = originalRuntimeCode)
    (budget : 2 + recordHashCost steps ≤ state.clock) :
    RunBounded state (recordHashAllocation count steps) (2 + recordHashCost steps) := by
  let argument : ExpHOL 64 := .panop .mul [.const count,.const 32]
  have args : evalListHOLFinite state (h := fun a => Classical.propDecidable (state.memaddrs a)) [argument] =
      some [.val (.word (count * (32#64)))] := by
    simp [argument,evalListHOLExact,evalHOLExact,panOpHOL,isWfShapeExactHOL,valueIsWord,valueWord]
  have reached := evaluate_allocation_declaration_reaches state argument (ofString "ch") heap (count * (32#64))
    (recordHashSuffix steps count) args code hh cap (by omega)
  exact evaluate_reaches_terminal_bounded state (recordHashAllocation count steps) (recordHashSuffix steps count) _ 2 _ budget reached (by
    intro next facts remaining
    obtain ⟨locals,_,installed,_,globals,newCap,_,_⟩ := facts
    have keep (key : MlS) (different : key ≠ ofString "ch") : next.locals.lookup key = state.locals.lookup key := by
      rw [locals]
      simp [HolFiniteMapExact.lookup_update,FUPDATE,Ne.symm different]
    exact recordHash_suffix_bound steps count small countBound next e heap out (allocationEnd heap (count * (32#64)))
      ⟨(keep _ (by decide)).trans atInput,(by rw [locals]; simp [HolFiniteMapExact.lookup_update,FUPDATE]),
        (keep _ (by decide)).trans atOut⟩
      (by rw [globals]; simp [setGlobalHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]) newCap (installed.trans code) remaining)

theorem recordHash_body_bound {F : Type} (state : PanSemStateFiniteExact 64 F)
    (count e out heap : BitVec 64) (steps : List RecordHashStep)
    (atInput : state.locals.lookup (ofString "e") = some (.val (.word e)))
    (atOut : state.locals.lookup (ofString "out") = some (.val (.word out)))
    (hh : state.globals.lookup (ofString "heap_ptr") = some (.val (.word heap)))
    (cap : heap.toNat ≤ 33806089496) (small : ∀ step ∈ steps, step.Small)
    (countBound : count.toNat ≤ 134217712) (code : state.code = originalRuntimeCode)
    (budget : 1 + (2 + recordHashCost steps) ≤ state.clock) :
    RunBounded state (recordHashBody count steps) (1 + (2 + recordHashCost steps)) := by
  have reached := evaluate_heapMark_declaration_reaches state (ofString "mark") heap
    (recordHashAllocation count steps) code hh (by omega)
  exact evaluate_reaches_terminal_bounded state (recordHashBody count steps) (recordHashAllocation count steps) _ 1 _ budget reached (by
    intro next facts remaining
    obtain ⟨locals,_,globals,installed,_⟩ := facts
    have keep (key : MlS) (different : key ≠ ofString "mark") : next.locals.lookup key = state.locals.lookup key := by
      rw [locals]
      simp [HolFiniteMapExact.lookup_update,FUPDATE,Ne.symm different]
    exact recordHash_allocation_bound next count e out heap steps ((keep _ (by decide)).trans atInput)
      ((keep _ (by decide)).trans atOut) (by rw [globals]; exact hh) cap small countBound (installed.trans code) remaining)

#print axioms recordHash_allocation_bound
#print axioms recordHash_body_bound
end InitECandidate.Runtime
