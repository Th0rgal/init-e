import ActualCandidateScratchEval
import InitECandidate.Runtime.GuestCostChargeFamily

namespace BoundedTableExperiment

open InitECandidate.Runtime
open InitECandidate.Runtime.FineCost
open Flapjack
open Flapjack.Pancake.PanLang
open Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- Actual keys allocation: with the shared allocator installed, `cap` and
`stride` word locals, and enough space for `cap * stride`, the frozen candidate
`keys <- scratch_alloc(cap * stride)` call succeeds and binds the returned
pointer in any continuation. -/
theorem candidate_keys_alloc_eval {F : Type} (state : PanSemStateFiniteExact 64 F)
    (pointer frame cap stride : BitVec 64)
    (capLocal : state.locals.lookup (ofString "cap") = some (.val (.word cap)))
    (strideLocal : state.locals.lookup (ofString "stride") = some (.val (.word stride)))
    (installed : state.code.lookup (ofString "scratch_alloc") =
      some ([(ofString "n",.one)],sourceFunctionBody Guest.guestFn_scratch_alloc,.one))
    (clock : state.clock ≠ 0)
    (scratchGlobal : state.globals.lookup (ofString "scratch_ptr") =
      some (.val (.word pointer)))
    (frameGlobal : state.globals.lookup (ofString "frame_mem_ptr") =
      some (.val (.word frame)))
    (request : cap * stride ≤ pointer - frame)
    (finishBound : frame ≤ scratchAllocationEnd pointer (cap * stride)) :
    ∃ ready : PanSemStateFiniteExact 64 F,
      evaluateHOLFiniteState state
          (.call (some (none,none)) (ofString "scratch_alloc")
            [.panop .mul [.var .local (ofString "cap"),
              .var .local (ofString "stride")]]) = (none,ready) ∧
      ready.memory = state.memory ∧
      ready.globals = (setGlobalHOLFinite (ofString "scratch_ptr")
        (.val (.word (scratchAllocationEnd pointer (cap * stride)))) state).globals ∧
      ∀ continuation,
        evaluateHOLFiniteState state
            (.decCall (ofString "keys") .one (ofString "scratch_alloc")
              [.panop .mul [.var .local (ofString "cap"),
                .var .local (ofString "stride")]] continuation) =
          (let output := evaluateHOLFiniteState
              (setVarHOLFinite (ofString "keys")
                (.val (.word (scratchAllocationEnd pointer (cap * stride)))) ready)
              continuation;
            (output.1,{output.2 with locals := (HolFiniteMapExact.resVarEq output.2.locals
              (ofString "keys",state.locals.lookup (ofString "keys")))})) := by
  have args : evalListHOLFinite state
      (h := fun address => Classical.propDecidable (state.memaddrs address))
      [.panop .mul [.var .local (ofString "cap"),
        .var .local (ofString "stride")]] = some [.val (.word (cap * stride))] := by
    simp [evalListHOLFinite, evalListHOLExact, evalHOLExact, capLocal, strideLocal,
      valueIsWord, panOpHOL, valueWord]
  obtain ⟨ready, call, _, memory, _, _, _, _, _, globals, cont⟩ :=
    candidate_scratch_alloc_call_and_declaration state
      (.panop .mul [.var .local (ofString "cap"), .var .local (ofString "stride")])
      pointer (cap * stride) frame args installed clock scratchGlobal frameGlobal
      request finishBound
  exact ⟨ready, call, memory, globals, fun continuation =>
    cont (ofString "keys") continuation⟩

end BoundedTableExperiment

#print axioms BoundedTableExperiment.candidate_keys_alloc_eval
