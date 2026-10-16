import InitECandidate.Runtime.AllocationPointerStore
import InitECandidate.Runtime.HashNewZero
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

def htabNewFinalAllocation : ProgHOL 64 :=
  match htabNewAfterZero with | .decCall _ _ _ _ (.seq _ rest) => rest | _ => .skip

theorem source_htabNew_final_allocation : htabNewFinalAllocation =
    .decCall (ofString "order_pos") .one (ofString "alloc")
      [.panop .mul [.var .local (ofString "cap"),.const 8]]
      (.seq (.store (hashLocalAddress (ofString "t") 64) (.var .local (ofString "order_pos")))
        (.return (.var .local (ofString "t")))) := by rfl

/-- The last original constructor allocation stores its pointer and returns
the table using exactly one source clock. -/
theorem evaluate_htabNew_final_allocation {F : Type} (state : PanSemStateFiniteExact 64 F)
    (pointer table capacity : BitVec 64)
    (code : state.code = originalRuntimeCode) (clock : state.clock ≠ 0)
    (heapGlobal : state.globals.lookup (ofString "heap_ptr") = some (.val (.word pointer)))
    (request : capacity * 8 ≤ (33806089496 : BitVec 64) - pointer)
    (finishBound : (allocationEnd pointer (capacity * 8)).toNat ≤ 33806089496)
    (tableLocal : state.locals.lookup (ofString "t") = some (.val (.word table)))
    (capLocal : state.locals.lookup (ofString "cap") = some (.val (.word capacity)))
    (domain : state.memaddrs (table + 64)) :
    ∃ post, evaluateHOLFiniteState state htabNewFinalAllocation = (some (.returned (.val (.word table))),post) ∧
      post.clock = state.clock - 1 ∧ post.memory (table + 64) = .word pointer ∧
      post.code = state.code ∧ post.memaddrs = state.memaddrs ∧ post.be = state.be ∧
      post.memory = (sourceWriteWord state (table + 64) pointer).memory ∧
      ∀ used slots : BitVec 64,
        (∀ index : BitVec 64, index.toNat < slots.toNat → panByteAlignHOL (used + index) ≠ table + 64) →
        hashOccupiedCount slots (hashOccupancyRead post used) = hashOccupiedCount slots (hashOccupancyRead state used) := by
  have arguments : evalListHOLFinite state
      (h := fun address => Classical.propDecidable (state.memaddrs address))
      [.panop .mul [.var .local (ofString "cap"),.const 8]] = some [.val (.word (capacity * 8))] := by
    simp [evalListHOLFinite,evalListHOLExact,evalHOLExact,capLocal,panOpHOL,valueIsWord,valueWord]
  obtain ⟨ready,run,ticks,locals,memory,stored,_,postCode,addresses,endian⟩ :=
    evaluate_allocation_pointer_store state (ofString "order_pos") (ofString "t") _ pointer (capacity * 8)
      table 64 (.return (.var .local (ofString "t"))) (by decide) arguments code clock heapGlobal
      request finishBound tableLocal domain
  have different : ofString "order_pos" ≠ ofString "t" := by decide
  have t : ready.locals.lookup (ofString "t") = some (.val (.word table)) := by
    rw [locals]
    simpa [setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,different] using tableLocal
  have returned : evaluateHOLFiniteState ready (.return (.var .local (ofString "t"))) =
      (some (.returned (.val (.word table))),emptyLocalsHOLFinite ready) := by
    simp [evaluateHOLFiniteState_return,evalHOLExact,t,shapeOfHOLExact]
  rw [source_htabNew_final_allocation,run]
  rw [returned]
  refine ⟨_,rfl,ticks,stored,postCode,addresses,endian,memory,?_⟩
  intro used slots separate
  have count := sourceWriteWord_occupancy_preserved state slots used (table + 64) pointer separate
  apply Eq.trans _ count
  apply hashOccupiedCount_congr
  intro index _
  change hashOccupancyRead ready used index = hashOccupancyRead (sourceWriteWord state (table + 64) pointer) used index
  unfold hashOccupancyRead
  rw [memory,addresses,endian]
  rfl

#print axioms source_htabNew_final_allocation
#print axioms evaluate_htabNew_final_allocation
end InitECandidate.Runtime
