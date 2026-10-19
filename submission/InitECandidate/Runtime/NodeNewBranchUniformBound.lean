import InitECandidate.Runtime.NodeNewBranchBody
import InitECandidate.Runtime.MemzeroCallBound
import InitECandidate.Runtime.AllocationUniformBound
import InitECandidate.Runtime.BoundedDecCallReach
import InitECandidate.Runtime.RunBoundedReaches
import InitECandidate.Runtime.TwoWordValueShape
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- Original branch initialization is bounded even with inaccessible memory or
an unaligned destination. -/
theorem runBounded_node_new_branch_initialize {F : Type} (s : PanSemStateFiniteExact 64 F)
    (pointer : BitVec 64) (atNode : s.locals.lookup (ofString "nd") = some (.val (.word pointer)))
    (code : s.code = originalRuntimeCode) (budget : 38 ≤ s.clock) :
    RunBounded s nodeNewBranchInitialize 38 := by
  rw [source_nodeNewBranch_initialize]
  have args : evalListHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a))
      [.var .local (ofString "nd"),.const 176] = some [.val (.word pointer),.val (.word (176#64))] := by
    rw [evalListHOLFinite_eq_toExact]
    simp [evalListHOLExact,evalHOLExact,atNode]
  have first := evaluate_memzero_call_bounded s _ pointer 176 args code (by decide) (by simpa using budget)
  have bound : RunBounded s (.call (some (none,none)) (ofString "memzero")
      [.var .local (ofString "nd"),.const 176]) 38 := by
    simpa [RunBounded] using first
  have tailBound : ProgBounded
      (.seq (.store (.op .add [.var .local (ofString "nd"),.const 0]) (.const 3))
        (.return (.var .local (ofString "nd")))) 0 := ProgBounded.straight _ rfl
  exact RunBounded.seq (b := 0) bound (by omega) (by
    intro next normal nextCode ticks
    exact RunBounded.ofProg tailBound (nextCode.trans code) (by omega))

/-- A uniform 40-tick bound for the complete original constructor. Real allocator
rejection and memory errors are included; no reserve or memory-domain premise is used. -/
theorem runBounded_node_new_branch_body {F : Type} (s : PanSemStateFiniteExact 64 F)
    (code : s.code = originalRuntimeCode) (budget : 40 ≤ s.clock) :
    RunBounded s (sourceFunctionBody Guest.guestFn_node_new_branch) 40 := by
  let callee : HolFiniteMapExact MlS (ValueHOL 64) :=
    HolFiniteMapExact.empty.update (ofString "n",.val (.word (176#64)))
  let entry := callEntryStateHOLFinite s callee
  have args : evalListHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a)) [.const 176] =
      some [.val (.word (176#64))] := by rw [evalListHOLFinite_eq_toExact]; rfl
  have lookup := pan_single_word_lookup s.code.lookup (ofString "alloc") (ofString "n")
    (sourceFunctionBody Guest.guestFn_alloc) 176 (by rw [code]; exact originalRuntimeCode_allocation_lookup)
  have allocBound := evaluate_source_alloc_uniform_bounded entry code (by change 1 ≤ s.clock - 1; omega)
  have bounded : RunBounded entry (sourceFunctionBody Guest.guestFn_alloc) 1 := ⟨allocBound.1,allocBound.2.1,allocBound.2.2.1⟩
  have reached : Reaches s (sourceFunctionBody Guest.guestFn_node_new_branch)
      (fun next => (∃ pointer : BitVec 64, next.locals.lookup (ofString "nd") = some (.val (.word pointer))) ∧
        next.code = originalRuntimeCode) 2 nodeNewBranchInitialize := by
    rw [source_nodeNewBranch_body]
    apply bounded_decCall_reaches s (ofString "nd") (ofString "alloc") .one .one _ _ _ _ callee 1 _
      args lookup (by omega) bounded
    intro value post run shapes
    obtain ⟨pointer,rfl⟩ := value_word_of_shape_one value ((shapeEqHOL_eq_true _ _).mp shapes.1)
    have metadata := evaluateHOLFiniteState_metadata entry (sourceFunctionBody Guest.guestFn_alloc)
    rw [run] at metadata
    exact ⟨⟨pointer,by simp [setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]⟩,metadata.1.trans code⟩
  exact RunBounded.ofReaches budget reached (by
    intro next facts ticks
    obtain ⟨⟨pointer,atNode⟩,nextCode⟩ := facts
    exact runBounded_node_new_branch_initialize next pointer atNode nextCode ticks)

#print axioms runBounded_node_new_branch_initialize
#print axioms runBounded_node_new_branch_body
end InitECandidate.Runtime
