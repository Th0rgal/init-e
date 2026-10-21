import ActualCandidateKeysHead
import InitECandidate.Runtime.ScratchAllocationCall

namespace BoundedTableExperiment

open InitECandidate.Runtime
open Flapjack
open Flapjack.Pancake.PanLang
open Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- Successful `scratch_alloc` call and declaration-call evaluation, requiring
only the shared allocator entry rather than the original runtime code. -/
theorem candidate_scratch_alloc_call_and_declaration {F : Type}
    (state : PanSemStateFiniteExact 64 F) (argument : ExpHOL 64)
    (pointer size frame : BitVec 64)
    (arguments : evalListHOLFinite state
      (h := fun address => Classical.propDecidable (state.memaddrs address))
      [argument] = some [.val (.word size)])
    (installed : state.code.lookup (ofString "scratch_alloc") =
      some ([(ofString "n",.one)],sourceFunctionBody Guest.guestFn_scratch_alloc,.one))
    (clock : state.clock ≠ 0)
    (scratchGlobal : state.globals.lookup (ofString "scratch_ptr") = some (.val (.word pointer)))
    (frameGlobal : state.globals.lookup (ofString "frame_mem_ptr") = some (.val (.word frame)))
    (request : size ≤ pointer - frame)
    (finishBound : frame ≤ scratchAllocationEnd pointer size) :
    ∃ ready, evaluateHOLFiniteState state
        (.call (some (none,none)) (ofString "scratch_alloc") [argument]) = (none,ready) ∧
      ready.clock = state.clock - 1 ∧ ready.memory = state.memory ∧
      ready.locals = state.locals ∧ ready.code = state.code ∧
      ready.memaddrs = state.memaddrs ∧ ready.eshapes = state.eshapes ∧
      ready.be = state.be ∧
      ready.globals = (setGlobalHOLFinite (ofString "scratch_ptr")
        (.val (.word (scratchAllocationEnd pointer size))) state).globals ∧
      ∀ name continuation,
        evaluateHOLFiniteState state
            (.decCall name .one (ofString "scratch_alloc") [argument] continuation) =
          (let output := evaluateHOLFiniteState
              (setVarHOLFinite name (.val (.word (scratchAllocationEnd pointer size))) ready)
              continuation;
            (output.1,{output.2 with locals := (HolFiniteMapExact.resVarEq output.2.locals
              (name,state.locals.lookup name))})) := by
  let callee : HolFiniteMapExact MlS (ValueHOL 64) :=
    HolFiniteMapExact.empty.update (ofString "n",.val (.word size))
  let entry := callEntryStateHOLFinite state callee
  have sizeLocal : entry.locals.lookup (ofString "n") = some (.val (.word size)) := by
    simp [entry,callEntryStateHOLFinite,callee,HolFiniteMapExact.lookup_update,FUPDATE]
  obtain ⟨post,body,heap,ticks,memory,postCode,domain,shapes,endian,globals⟩ :=
    evaluate_source_scratch_alloc_success entry pointer size frame scratchGlobal sizeLocal
      frameGlobal request finishBound
  have lookup := pan_single_word_lookup state.code.lookup (ofString "scratch_alloc")
    (ofString "n") (sourceFunctionBody Guest.guestFn_scratch_alloc) size installed
  have shapeOk : shapeEqHOL (shapeOfHOLExact (.val (.word (scratchAllocationEnd pointer size))))
      .one = true := by
    simp [shapeOfHOLExact,shapeEqHOL]
  have call := evaluateHOLFiniteState_call_return_caller_locals state none
    (ofString "scratch_alloc") [argument] [.val (.word size)]
    (sourceFunctionBody Guest.guestFn_scratch_alloc) callee .one
    (.val (.word (scratchAllocationEnd pointer size))) post arguments lookup clock body shapeOk
  refine ⟨{post with locals := state.locals},call,ticks,memory,rfl,postCode,domain,shapes,
    endian,globals,?_⟩
  intro name continuation
  exact evaluate_decCall_return_caller_locals state post name (ofString "scratch_alloc")
    .one .one [argument] [.val (.word size)]
    (sourceFunctionBody Guest.guestFn_scratch_alloc) continuation callee
    (.val (.word (scratchAllocationEnd pointer size))) arguments lookup clock body
    (Nat.le_of_eq ticks) shapeOk shapeOk

end BoundedTableExperiment

#print axioms BoundedTableExperiment.candidate_scratch_alloc_call_and_declaration

namespace BoundedTableExperiment

open InitECandidate.Runtime
open Flapjack
open Flapjack.Pancake.PanLang
open Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- The frozen candidate `htab_new_scratch` actually performs its first
120-byte table allocation: with the shared allocator installed and enough
space, the body evaluates to the continuation with `t` bound to the returned
end pointer and the scratch frontier advanced. -/
theorem candidate_htabNewScratch_first_alloc_eval {F : Type}
    (state : PanSemStateFiniteExact 64 F) (pointer frame : BitVec 64)
    (installed : state.code.lookup (ofString "scratch_alloc") =
      some ([(ofString "n",.one)],sourceFunctionBody Guest.guestFn_scratch_alloc,.one))
    (clock : state.clock ≠ 0)
    (scratchGlobal : state.globals.lookup (ofString "scratch_ptr") =
      some (.val (.word pointer)))
    (frameGlobal : state.globals.lookup (ofString "frame_mem_ptr") =
      some (.val (.word frame)))
    (request : BitVec.ofNat 64 120 ≤ pointer - frame)
    (finishBound : frame ≤ scratchAllocationEnd pointer (BitVec.ofNat 64 120)) :
    ∃ (rest : ProgHOL 64) (ready : PanSemStateFiniteExact 64 F),
      sourceFunctionBody CandidateGuest.guestFn_htab_new_scratch =
        .decCall (ofString "t") .one (ofString "scratch_alloc")
          [.const (BitVec.ofNat 64 120)] rest ∧
      evaluateHOLFiniteState state
          (.call (some (none,none)) (ofString "scratch_alloc")
            [.const (BitVec.ofNat 64 120)]) = (none,ready) ∧
      ready.clock = state.clock - 1 ∧ ready.memory = state.memory ∧
      ready.globals = (setGlobalHOLFinite (ofString "scratch_ptr")
        (.val (.word (scratchAllocationEnd pointer (BitVec.ofNat 64 120)))) state).globals ∧
      evaluateHOLFiniteState state
          (sourceFunctionBody CandidateGuest.guestFn_htab_new_scratch) =
        (let output := evaluateHOLFiniteState
            (setVarHOLFinite (ofString "t")
              (.val (.word (scratchAllocationEnd pointer (BitVec.ofNat 64 120)))) ready)
            rest;
          (output.1,{output.2 with locals := (HolFiniteMapExact.resVarEq output.2.locals
            (ofString "t",state.locals.lookup (ofString "t")))})) := by
  obtain ⟨rest, head⟩ := candidate_htabNewScratch_allocHead
  have args : evalListHOLFinite state
      (h := fun address => Classical.propDecidable (state.memaddrs address))
      [.const (BitVec.ofNat 64 120)] = some [.val (.word (BitVec.ofNat 64 120))] := by
    simp [evalListHOLFinite, evalListHOLExact, evalHOLExact, evalHOLFinite]
  obtain ⟨ready, call, readyClock, readyMemory, _, _, _, _, _, readyGlobals, continuation⟩ :=
    candidate_scratch_alloc_call_and_declaration state
      (.const (BitVec.ofNat 64 120)) pointer (BitVec.ofNat 64 120) frame args
      installed clock scratchGlobal frameGlobal request finishBound
  refine ⟨rest, ready, head, call, readyClock, readyMemory, readyGlobals, ?_⟩
  rw [head]
  exact continuation (ofString "t") rest

end BoundedTableExperiment

#print axioms BoundedTableExperiment.candidate_htabNewScratch_first_alloc_eval
