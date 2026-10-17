import InitECandidate.Runtime.RlpHeaderCallBound
import InitECandidate.Runtime.PanDecCallNormalReturnState
import InitECandidate.Runtime.RlpHeaderUniformGlobals
import InitECandidate.Runtime.RlpHeaderUniformMemory
import InitECandidate.Runtime.RlpHeaderCallSizedMemory
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- Normal completion of the actual header-reader declaration-call binds a
validated header before executing its original caller continuation. -/
theorem evaluate_rlpHeader_decCall_normal_state {F : Type} (state post : PanSemStateFiniteExact 64 F)
    (name : MlS) (arguments : List (ExpHOL 64)) (continuation : ProgHOL 64)
    (pointer length : BitVec 64)
    (args : evalListHOLFinite state (h := fun address => Classical.propDecidable (state.memaddrs address)) arguments =
      some [.val (.word pointer),.val (.word length)])
    (code : state.code = originalRuntimeCode) (ticks : 12 ≤ state.clock)
    (run : evaluateHOLFiniteState state (.decCall name (.comb [.one,.one,.one]) (ofString "rlp_item_header") arguments continuation) = (none,post)) :
    ∃ (value : ValueHOL 64) (ready output : PanSemStateFiniteExact 64 F), RlpHeaderSizedProgress value length ∧ ready.locals = state.locals ∧ ready.memory = state.memory ∧
      ready.globals = state.globals ∧ ready.code = state.code ∧ ready.memaddrs = state.memaddrs ∧
      ready.clock ≤ state.clock ∧ state.clock ≤ ready.clock + 12 ∧
      evaluateHOLFiniteState (setVarHOLFinite name value ready) continuation = (none,output) ∧
      post = {output with locals := HolFiniteMapExact.resVarEq output.locals (name,state.locals.lookup name)} := by
  let callee := rlpHeaderCallee pointer length
  let entry := callEntryStateHOLFinite state callee
  have pointerLocal : entry.locals.lookup (ofString "p") = some (.val (.word pointer)) := by
    simp [entry,callEntryStateHOLFinite,callee,rlpHeaderCallee,HolFiniteMapExact.lookup_update,FUPDATE,
      show ofString "len" ≠ ofString "p" by decide]
  have lengthLocal : entry.locals.lookup (ofString "len") = some (.val (.word length)) := by
    simp [entry,callEntryStateHOLFinite,callee,rlpHeaderCallee,HolFiniteMapExact.lookup_update,FUPDATE]
  obtain ⟨bodyResult,bodyPost,bodyRun,cost,remaining,_,_,returned⟩ := evaluate_rlpHeader_uniform_contract entry pointer length
    pointerLocal lengthLocal code (by change 11 ≤ state.clock - 1; omega)
  have installed : state.code.lookup (ofString "rlp_item_header") =
      some ([(ofString "p",.one),(ofString "len",.one)],sourceFunctionBody Guest.guestFn_rlp_item_header,.comb [.one,.one,.one]) := by
    rw [code]; exact originalRuntimeCode_rlpHeader_lookup
  have lookup := pan_two_word_lookup_shape state.code.lookup (ofString "rlp_item_header")
    (ofString "p") (ofString "len") (sourceFunctionBody Guest.guestFn_rlp_item_header) (.comb [.one,.one,.one]) pointer length (by decide) installed
  let property := fun value : ValueHOL 64 => RlpHeaderSizedProgress value length
  have bodyProperty : ∀ value output, evaluateHOLFiniteState entry (sourceFunctionBody Guest.guestFn_rlp_item_header) =
      (some (.returned value),output) → property value := by
    intro value output evaluated
    have same := (Prod.mk.inj (bodyRun.symm.trans evaluated)).1
    exact ⟨returned value same,rlpHeader_uniform_return_sizes entry output pointer length value
      pointerLocal lengthLocal code (by change 11 ≤ state.clock - 1; omega) evaluated⟩
  have bodyFrame : ∀ value output, evaluateHOLFiniteState entry (sourceFunctionBody Guest.guestFn_rlp_item_header) =
      (some (.returned value),output) → output.memory = state.memory ∧ output.globals = state.globals ∧
        output.clock ≤ entry.clock ∧ state.clock ≤ output.clock + 12 := by
    intro value output evaluated
    have same := (Prod.mk.inj (bodyRun.symm.trans evaluated)).2
    subst output
    have memory := rlpHeader_uniform_returned_memory entry bodyPost pointer length value pointerLocal lengthLocal code
      (by change 11 ≤ state.clock - 1; omega) evaluated
    have globals := rlpHeader_uniform_returned_globals entry bodyPost pointer length value pointerLocal lengthLocal code
      (by change 11 ≤ state.clock - 1; omega) evaluated
    have entryClock : entry.clock = state.clock - 1 := rfl
    exact ⟨memory,globals,remaining,by omega⟩
  obtain ⟨value,ready,output,valid,locals,memory,globals,readyCode,domain,remainingClock,clockBound,tail,restored⟩ := evaluate_decCall_normal_return_state
    state post name (ofString "rlp_item_header") (.comb [.one,.one,.one]) (.comb [.one,.one,.one]) arguments [.val (.word pointer),.val (.word length)]
    (sourceFunctionBody Guest.guestFn_rlp_item_header) continuation callee args lookup 12 property bodyProperty bodyFrame run
  exact ⟨value,ready,output,valid,locals,memory,globals,readyCode,domain,remainingClock,clockBound,tail,restored⟩

#print axioms evaluate_rlpHeader_decCall_normal_state
end InitECandidate.Runtime
