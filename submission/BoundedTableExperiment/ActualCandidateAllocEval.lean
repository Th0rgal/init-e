import ActualCandidateKeysEval

namespace BoundedTableExperiment

open InitECandidate.Runtime
open InitECandidate.Runtime.FineCost
open Flapjack
open Flapjack.Pancake.PanLang
open Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- Generic actual allocation: one frozen candidate scratch_alloc call with
already-evaluated single word argument. -/
theorem candidate_alloc_eval_general {F : Type} (state : PanSemStateFiniteExact 64 F)
    (name : MlS) (argument : ExpHOL 64) (size : BitVec 64)
    (pointer frame : BitVec 64)
    (arguments : evalListHOLFinite state
      (h := fun address => Classical.propDecidable (state.memaddrs address))
      [argument] = some [.val (.word size)])
    (installed : state.code.lookup (ofString "scratch_alloc") =
      some ([(ofString "n",.one)],sourceFunctionBody Guest.guestFn_scratch_alloc,.one))
    (clock : state.clock ≠ 0)
    (scratchGlobal : state.globals.lookup (ofString "scratch_ptr") =
      some (.val (.word pointer)))
    (frameGlobal : state.globals.lookup (ofString "frame_mem_ptr") =
      some (.val (.word frame)))
    (request : size ≤ pointer - frame)
    (finishBound : frame ≤ scratchAllocationEnd pointer size) :
    ∃ ready : PanSemStateFiniteExact 64 F,
      evaluateHOLFiniteState state
          (.call (some (none,none)) (ofString "scratch_alloc") [argument]) = (none,ready) ∧
      ready.memory = state.memory ∧
      ready.globals = (setGlobalHOLFinite (ofString "scratch_ptr")
        (.val (.word (scratchAllocationEnd pointer size))) state).globals ∧
      ∀ continuation,
        evaluateHOLFiniteState state
            (.decCall name .one (ofString "scratch_alloc") [argument] continuation) =
          (let output := evaluateHOLFiniteState
              (setVarHOLFinite name (.val (.word (scratchAllocationEnd pointer size))) ready)
              continuation;
            (output.1,{output.2 with locals := (HolFiniteMapExact.resVarEq output.2.locals
              (name,state.locals.lookup name))})) := by
  obtain ⟨ready, call, _, memory, _, _, _, _, _, globals, cont⟩ :=
    candidate_scratch_alloc_call_and_declaration state argument pointer size frame
      arguments installed clock scratchGlobal frameGlobal request finishBound
  exact ⟨ready, call, memory, globals, fun continuation =>
    cont name continuation⟩

/-- `vals <- scratch_alloc(cap * 8)` succeeds. -/
theorem candidate_vals_alloc_eval {F : Type} (state : PanSemStateFiniteExact 64 F)
    (pointer frame cap : BitVec 64)
    (capLocal : state.locals.lookup (ofString "cap") = some (.val (.word cap)))
    (installed : state.code.lookup (ofString "scratch_alloc") =
      some ([(ofString "n",.one)],sourceFunctionBody Guest.guestFn_scratch_alloc,.one))
    (clock : state.clock ≠ 0)
    (scratchGlobal : state.globals.lookup (ofString "scratch_ptr") =
      some (.val (.word pointer)))
    (frameGlobal : state.globals.lookup (ofString "frame_mem_ptr") =
      some (.val (.word frame)))
    (request : cap * BitVec.ofNat 64 8 ≤ pointer - frame)
    (finishBound : frame ≤ scratchAllocationEnd pointer (cap * BitVec.ofNat 64 8)) :
    ∃ ready : PanSemStateFiniteExact 64 F,
      evaluateHOLFiniteState state
          (.call (some (none,none)) (ofString "scratch_alloc")
            [.panop .mul [.var .local (ofString "cap"),
              .const (BitVec.ofNat 64 8)]]) = (none,ready) ∧
      ready.memory = state.memory ∧
      ready.globals = (setGlobalHOLFinite (ofString "scratch_ptr")
        (.val (.word (scratchAllocationEnd pointer (cap * BitVec.ofNat 64 8)))) state).globals ∧
      ∀ continuation,
        evaluateHOLFiniteState state
            (.decCall (ofString "vals") .one (ofString "scratch_alloc")
              [.panop .mul [.var .local (ofString "cap"),
                .const (BitVec.ofNat 64 8)]] continuation) =
          (let output := evaluateHOLFiniteState
              (setVarHOLFinite (ofString "vals")
                (.val (.word (scratchAllocationEnd pointer (cap * BitVec.ofNat 64 8)))) ready)
              continuation;
            (output.1,{output.2 with locals := (HolFiniteMapExact.resVarEq output.2.locals
              (ofString "vals",state.locals.lookup (ofString "vals")))})) := by
  have args : evalListHOLFinite state
      (h := fun address => Classical.propDecidable (state.memaddrs address))
      [.panop .mul [.var .local (ofString "cap"), .const (BitVec.ofNat 64 8)]] =
      some [.val (.word (cap * BitVec.ofNat 64 8))] := by
    simp [evalListHOLFinite, evalListHOLExact, evalHOLExact, capLocal,
      valueIsWord, panOpHOL, valueWord]
  exact candidate_alloc_eval_general state (ofString "vals")
    (.panop .mul [.var .local (ofString "cap"), .const (BitVec.ofNat 64 8)])
    (cap * BitVec.ofNat 64 8) pointer frame args installed clock scratchGlobal
    frameGlobal request finishBound

/-- `order <- scratch_alloc(cap * 8)` succeeds. -/
theorem candidate_order_alloc_eval {F : Type} (state : PanSemStateFiniteExact 64 F)
    (pointer frame cap : BitVec 64)
    (capLocal : state.locals.lookup (ofString "cap") = some (.val (.word cap)))
    (installed : state.code.lookup (ofString "scratch_alloc") =
      some ([(ofString "n",.one)],sourceFunctionBody Guest.guestFn_scratch_alloc,.one))
    (clock : state.clock ≠ 0)
    (scratchGlobal : state.globals.lookup (ofString "scratch_ptr") =
      some (.val (.word pointer)))
    (frameGlobal : state.globals.lookup (ofString "frame_mem_ptr") =
      some (.val (.word frame)))
    (request : cap * BitVec.ofNat 64 8 ≤ pointer - frame)
    (finishBound : frame ≤ scratchAllocationEnd pointer (cap * BitVec.ofNat 64 8)) :
    ∃ ready : PanSemStateFiniteExact 64 F,
      evaluateHOLFiniteState state
          (.call (some (none,none)) (ofString "scratch_alloc")
            [.panop .mul [.var .local (ofString "cap"),
              .const (BitVec.ofNat 64 8)]]) = (none,ready) ∧
      ready.memory = state.memory ∧
      ready.globals = (setGlobalHOLFinite (ofString "scratch_ptr")
        (.val (.word (scratchAllocationEnd pointer (cap * BitVec.ofNat 64 8)))) state).globals ∧
      ∀ continuation,
        evaluateHOLFiniteState state
            (.decCall (ofString "order") .one (ofString "scratch_alloc")
              [.panop .mul [.var .local (ofString "cap"),
                .const (BitVec.ofNat 64 8)]] continuation) =
          (let output := evaluateHOLFiniteState
              (setVarHOLFinite (ofString "order")
                (.val (.word (scratchAllocationEnd pointer (cap * BitVec.ofNat 64 8)))) ready)
              continuation;
            (output.1,{output.2 with locals := (HolFiniteMapExact.resVarEq output.2.locals
              (ofString "order",state.locals.lookup (ofString "order")))})) := by
  have args : evalListHOLFinite state
      (h := fun address => Classical.propDecidable (state.memaddrs address))
      [.panop .mul [.var .local (ofString "cap"), .const (BitVec.ofNat 64 8)]] =
      some [.val (.word (cap * BitVec.ofNat 64 8))] := by
    simp [evalListHOLFinite, evalListHOLExact, evalHOLExact, capLocal,
      valueIsWord, panOpHOL, valueWord]
  exact candidate_alloc_eval_general state (ofString "order")
    (.panop .mul [.var .local (ofString "cap"), .const (BitVec.ofNat 64 8)])
    (cap * BitVec.ofNat 64 8) pointer frame args installed clock scratchGlobal
    frameGlobal request finishBound

/-- `order_pos <- scratch_alloc(cap * 8)` succeeds. -/
theorem candidate_order_pos_alloc_eval {F : Type} (state : PanSemStateFiniteExact 64 F)
    (pointer frame cap : BitVec 64)
    (capLocal : state.locals.lookup (ofString "cap") = some (.val (.word cap)))
    (installed : state.code.lookup (ofString "scratch_alloc") =
      some ([(ofString "n",.one)],sourceFunctionBody Guest.guestFn_scratch_alloc,.one))
    (clock : state.clock ≠ 0)
    (scratchGlobal : state.globals.lookup (ofString "scratch_ptr") =
      some (.val (.word pointer)))
    (frameGlobal : state.globals.lookup (ofString "frame_mem_ptr") =
      some (.val (.word frame)))
    (request : cap * BitVec.ofNat 64 8 ≤ pointer - frame)
    (finishBound : frame ≤ scratchAllocationEnd pointer (cap * BitVec.ofNat 64 8)) :
    ∃ ready : PanSemStateFiniteExact 64 F,
      evaluateHOLFiniteState state
          (.call (some (none,none)) (ofString "scratch_alloc")
            [.panop .mul [.var .local (ofString "cap"),
              .const (BitVec.ofNat 64 8)]]) = (none,ready) ∧
      ready.memory = state.memory ∧
      ready.globals = (setGlobalHOLFinite (ofString "scratch_ptr")
        (.val (.word (scratchAllocationEnd pointer (cap * BitVec.ofNat 64 8)))) state).globals ∧
      ∀ continuation,
        evaluateHOLFiniteState state
            (.decCall (ofString "order_pos") .one (ofString "scratch_alloc")
              [.panop .mul [.var .local (ofString "cap"),
                .const (BitVec.ofNat 64 8)]] continuation) =
          (let output := evaluateHOLFiniteState
              (setVarHOLFinite (ofString "order_pos")
                (.val (.word (scratchAllocationEnd pointer (cap * BitVec.ofNat 64 8)))) ready)
              continuation;
            (output.1,{output.2 with locals := (HolFiniteMapExact.resVarEq output.2.locals
              (ofString "order_pos",state.locals.lookup (ofString "order_pos")))})) := by
  have args : evalListHOLFinite state
      (h := fun address => Classical.propDecidable (state.memaddrs address))
      [.panop .mul [.var .local (ofString "cap"), .const (BitVec.ofNat 64 8)]] =
      some [.val (.word (cap * BitVec.ofNat 64 8))] := by
    simp [evalListHOLFinite, evalListHOLExact, evalHOLExact, capLocal,
      valueIsWord, panOpHOL, valueWord]
  exact candidate_alloc_eval_general state (ofString "order_pos")
    (.panop .mul [.var .local (ofString "cap"), .const (BitVec.ofNat 64 8)])
    (cap * BitVec.ofNat 64 8) pointer frame args installed clock scratchGlobal
    frameGlobal request finishBound

/-- `nodes <- scratch_alloc((cap >> 1) * 24)` succeeds. -/
theorem candidate_nodes_alloc_eval {F : Type} (state : PanSemStateFiniteExact 64 F)
    (pointer frame cap : BitVec 64)
    (capLocal : state.locals.lookup (ofString "cap") = some (.val (.word cap)))
    (installed : state.code.lookup (ofString "scratch_alloc") =
      some ([(ofString "n",.one)],sourceFunctionBody Guest.guestFn_scratch_alloc,.one))
    (clock : state.clock ≠ 0)
    (scratchGlobal : state.globals.lookup (ofString "scratch_ptr") =
      some (.val (.word pointer)))
    (frameGlobal : state.globals.lookup (ofString "frame_mem_ptr") =
      some (.val (.word frame)))
    (request : cap.sshiftRight 1 * BitVec.ofNat 64 24 ≤ pointer - frame)
    (finishBound : frame ≤ scratchAllocationEnd pointer
      (cap.sshiftRight 1 * BitVec.ofNat 64 24)) :
    ∃ ready : PanSemStateFiniteExact 64 F,
      evaluateHOLFiniteState state
          (.call (some (none,none)) (ofString "scratch_alloc")
            [.panop .mul [.shift .asr (.var .local (ofString "cap"))
              (.const (BitVec.ofNat 64 1)), .const (BitVec.ofNat 64 24)]]) = (none,ready) ∧
      ready.memory = state.memory ∧
      ready.globals = (setGlobalHOLFinite (ofString "scratch_ptr")
        (.val (.word (scratchAllocationEnd pointer
          (cap.sshiftRight 1 * BitVec.ofNat 64 24)))) state).globals ∧
      ∀ continuation,
        evaluateHOLFiniteState state
            (.decCall (ofString "nodes") .one (ofString "scratch_alloc")
              [.panop .mul [.shift .asr (.var .local (ofString "cap"))
                (.const (BitVec.ofNat 64 1)), .const (BitVec.ofNat 64 24)]] continuation) =
          (let output := evaluateHOLFiniteState
              (setVarHOLFinite (ofString "nodes")
                (.val (.word (scratchAllocationEnd pointer
                  (cap.sshiftRight 1 * BitVec.ofNat 64 24)))) ready)
              continuation;
            (output.1,{output.2 with locals := (HolFiniteMapExact.resVarEq output.2.locals
              (ofString "nodes",state.locals.lookup (ofString "nodes")))})) := by
  have args : evalListHOLFinite state
      (h := fun address => Classical.propDecidable (state.memaddrs address))
      [.panop .mul [.shift .asr (.var .local (ofString "cap"))
        (.const (BitVec.ofNat 64 1)), .const (BitVec.ofNat 64 24)]] =
      some [.val (.word (cap.sshiftRight 1 * BitVec.ofNat 64 24))] := by
    simp [evalListHOLFinite, evalListHOLExact, evalHOLExact, capLocal,
      valueIsWord, panOpHOL, wordOp, wordShiftHOL, valueWord]
  exact candidate_alloc_eval_general state (ofString "nodes")
    (.panop .mul [.shift .asr (.var .local (ofString "cap"))
      (.const (BitVec.ofNat 64 1)), .const (BitVec.ofNat 64 24)])
    (cap.sshiftRight 1 * BitVec.ofNat 64 24) pointer frame args installed clock
    scratchGlobal frameGlobal request finishBound

/-- `path <- scratch_alloc(key_len * 64)` succeeds. -/
theorem candidate_path_alloc_eval {F : Type} (state : PanSemStateFiniteExact 64 F)
    (pointer frame keyLen : BitVec 64)
    (keyLocal : state.locals.lookup (ofString "key_len") = some (.val (.word keyLen)))
    (installed : state.code.lookup (ofString "scratch_alloc") =
      some ([(ofString "n",.one)],sourceFunctionBody Guest.guestFn_scratch_alloc,.one))
    (clock : state.clock ≠ 0)
    (scratchGlobal : state.globals.lookup (ofString "scratch_ptr") =
      some (.val (.word pointer)))
    (frameGlobal : state.globals.lookup (ofString "frame_mem_ptr") =
      some (.val (.word frame)))
    (request : keyLen * BitVec.ofNat 64 64 ≤ pointer - frame)
    (finishBound : frame ≤ scratchAllocationEnd pointer (keyLen * BitVec.ofNat 64 64)) :
    ∃ ready : PanSemStateFiniteExact 64 F,
      evaluateHOLFiniteState state
          (.call (some (none,none)) (ofString "scratch_alloc")
            [.panop .mul [.var .local (ofString "key_len"),
              .const (BitVec.ofNat 64 64)]]) = (none,ready) ∧
      ready.memory = state.memory ∧
      ready.globals = (setGlobalHOLFinite (ofString "scratch_ptr")
        (.val (.word (scratchAllocationEnd pointer (keyLen * BitVec.ofNat 64 64)))) state).globals ∧
      ∀ continuation,
        evaluateHOLFiniteState state
            (.decCall (ofString "path") .one (ofString "scratch_alloc")
              [.panop .mul [.var .local (ofString "key_len"),
                .const (BitVec.ofNat 64 64)]] continuation) =
          (let output := evaluateHOLFiniteState
              (setVarHOLFinite (ofString "path")
                (.val (.word (scratchAllocationEnd pointer (keyLen * BitVec.ofNat 64 64)))) ready)
              continuation;
            (output.1,{output.2 with locals := (HolFiniteMapExact.resVarEq output.2.locals
              (ofString "path",state.locals.lookup (ofString "path")))})) := by
  have args : evalListHOLFinite state
      (h := fun address => Classical.propDecidable (state.memaddrs address))
      [.panop .mul [.var .local (ofString "key_len"), .const (BitVec.ofNat 64 64)]] =
      some [.val (.word (keyLen * BitVec.ofNat 64 64))] := by
    simp [evalListHOLFinite, evalListHOLExact, evalHOLExact, keyLocal,
      valueIsWord, panOpHOL, valueWord]
  exact candidate_alloc_eval_general state (ofString "path")
    (.panop .mul [.var .local (ofString "key_len"), .const (BitVec.ofNat 64 64)])
    (keyLen * BitVec.ofNat 64 64) pointer frame args installed clock scratchGlobal
    frameGlobal request finishBound

end BoundedTableExperiment

#print axioms BoundedTableExperiment.candidate_vals_alloc_eval
#print axioms BoundedTableExperiment.candidate_order_alloc_eval
#print axioms BoundedTableExperiment.candidate_order_pos_alloc_eval
#print axioms BoundedTableExperiment.candidate_nodes_alloc_eval
#print axioms BoundedTableExperiment.candidate_path_alloc_eval

namespace BoundedTableExperiment

open InitECandidate.Runtime
open InitECandidate.Runtime.FineCost
open Flapjack
open Flapjack.Pancake.PanLang
open Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- The explicit ready state of a candidate scratch allocation call. -/
noncomputable def candidateAllocReady {F : Type} (state : PanSemStateFiniteExact 64 F)
    (argument : ExpHOL 64) : PanSemStateFiniteExact 64 F :=
  (evaluateHOLFiniteState state
    (.call (some (none,none)) (ofString "scratch_alloc") [argument])).2

/-- Explicit form of one candidate allocation: the ready state is the actual
second component of the call evaluation, so allocation results chain
definitionally. -/
theorem candidate_alloc_eval_explicit {F : Type} (state : PanSemStateFiniteExact 64 F)
    (name : MlS) (argument : ExpHOL 64) (size : BitVec 64)
    (pointer frame : BitVec 64)
    (arguments : evalListHOLFinite state
      (h := fun address => Classical.propDecidable (state.memaddrs address))
      [argument] = some [.val (.word size)])
    (installed : state.code.lookup (ofString "scratch_alloc") =
      some ([(ofString "n",.one)],sourceFunctionBody Guest.guestFn_scratch_alloc,.one))
    (clock : state.clock ≠ 0)
    (scratchGlobal : state.globals.lookup (ofString "scratch_ptr") =
      some (.val (.word pointer)))
    (frameGlobal : state.globals.lookup (ofString "frame_mem_ptr") =
      some (.val (.word frame)))
    (request : size ≤ pointer - frame)
    (finishBound : frame ≤ scratchAllocationEnd pointer size) :
    (candidateAllocReady state argument).memory = state.memory ∧
    (candidateAllocReady state argument).globals =
      (setGlobalHOLFinite (ofString "scratch_ptr")
        (.val (.word (scratchAllocationEnd pointer size))) state).globals ∧
    ∀ continuation,
      evaluateHOLFiniteState state
          (.decCall name .one (ofString "scratch_alloc") [argument] continuation) =
        (let output := evaluateHOLFiniteState
            (setVarHOLFinite name (.val (.word (scratchAllocationEnd pointer size)))
              (candidateAllocReady state argument))
            continuation;
          (output.1,{output.2 with locals := (HolFiniteMapExact.resVarEq output.2.locals
            (name,state.locals.lookup name))})) := by
  obtain ⟨ready, call, memory, globals, cont⟩ :=
    candidate_alloc_eval_general state name argument size pointer frame arguments
      installed clock scratchGlobal frameGlobal request finishBound
  have readyEq : candidateAllocReady state argument = ready := by
    simp [candidateAllocReady, call]
  refine ⟨?_, ?_, ?_⟩
  · rw [readyEq]; exact memory
  · rw [readyEq]; exact globals
  · intro continuation
    rw [readyEq]
    exact cont continuation

end BoundedTableExperiment

#print axioms BoundedTableExperiment.candidate_alloc_eval_explicit
