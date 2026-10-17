import InitECandidate.Runtime.RlpValidationHeaderCallState
import InitECandidate.Runtime.RlpValidationListInvariant
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- A normally completed original header-call/list path preserves validator
invariants through parsing, scratch allocation and scope restoration. -/
theorem rlpValidation_parse_list_invariant {F : Type} (state post : PanSemStateFiniteExact 64 F)
    (position stop scratch frame : BitVec 64) (frames : List RlpValidationFrame)
    (positionLocal : state.locals.lookup (ofString "pos") = some (.val (.word position)))
    (stopLocal : state.locals.lookup (ofString "end") = some (.val (.word stop)))
    (topLocal : state.locals.lookup (ofString "top") = some (.val (.word (rlpValidationStackTop frames))))
    (stack : RlpValidationStack state.memory scratch.toNat frames)
    (intervals : RlpValidationIntervals position stop frames)
    (inputBound : (stop - position).toNat + 9 < 2^64)
    (scratchGlobal : state.globals.lookup (ofString "scratch_ptr") = some (.val (.word scratch)))
    (frameGlobal : state.globals.lookup (ofString "frame_mem_ptr") = some (.val (.word frame)))
    (code : state.code = originalRuntimeCode) (ticks : 14 ≤ state.clock)
    (orderedFrame : frame ≤ scratch) (framePositive : 0 < frame.toNat)
    (arena : ∀ address : BitVec 64, frame.toNat ≤ address.toNat → address.toNat < scratch.toNat → state.memaddrs address)
    (run : evaluateHOLFiniteState state rlpValidationHeaderCall = (none,post)) :
    ∃ (header payload kind : BitVec 64) (ready output : PanSemStateFiniteExact 64 F),
      (kind = 0 ∨ kind = 1) ∧
      evaluateHOLFiniteState (setVarHOLFinite (ofString "h")
        (.rStruct [.val (.word header),.val (.word payload),.val (.word kind)]) ready)
        rlpValidationHeaderContinuation = (none,output) ∧
      post = {output with locals := HolFiniteMapExact.resVarEq output.locals (ofString "h",state.locals.lookup (ofString "h"))} ∧
      (kind = 1 →
        let record := scratchAllocationEnd scratch 24
        let extended := {record := record,resume := position + header + payload,stop := stop} :: frames
        post.locals.lookup (ofString "pos") = some (.val (.word (position + header))) ∧
        post.locals.lookup (ofString "end") = some (.val (.word (position + header + payload))) ∧
        post.locals.lookup (ofString "top") = some (.val (.word record)) ∧
        RlpValidationStack post.memory record.toNat extended ∧
        RlpValidationIntervals (position + header) (position + header + payload) extended ∧
        rlpValidationRank (position + header) (position + header + payload) extended < rlpValidationRank position stop frames ∧
        state.clock ≤ post.clock + 13) := by
  obtain ⟨value,ready,output,valid,locals,memory,globals,readyCode,domain,remaining,bound,tail,restored⟩ :=
    evaluate_rlpValidation_header_call_state state post position stop positionLocal stopLocal code (by omega) run
  obtain ⟨header,payload,kind,shape,_,_,_⟩ := valid.2
  subst value
  have fields := valid.fields header payload kind (stop - position)
  refine ⟨header,payload,kind,ready,output,fields.1,tail,restored,?_⟩
  intro list
  subst kind
  let entered := setVarHOLFinite (ofString "h")
    (.rStruct [.val (.word header),.val (.word payload),.val (.word 1)]) ready
  have localFrame : ∀ name, name ≠ ofString "h" → entered.locals.lookup name = state.locals.lookup name := by
    intro name different
    simp [entered,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,Ne.symm different,locals]
  have atHeader : entered.locals.lookup (ofString "h") = some
      (.rStruct [.val (.word header),.val (.word payload),.val (.word 1)]) := by
    simp [entered,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]
  have enteredStack : RlpValidationStack entered.memory scratch.toNat frames := by
    change RlpValidationStack ready.memory scratch.toNat frames
    rw [memory]; exact stack
  have atScratch : entered.globals.lookup (ofString "scratch_ptr") = some (.val (.word scratch)) := by
    change ready.globals.lookup _ = _
    rw [globals]; exact scratchGlobal
  have atFrame : entered.globals.lookup (ofString "frame_mem_ptr") = some (.val (.word frame)) := by
    change ready.globals.lookup _ = _
    rw [globals]; exact frameGlobal
  have arenaEntered : ∀ address : BitVec 64, frame.toNat ≤ address.toNat → address.toNat < scratch.toNat → entered.memaddrs address := by
    simpa only [entered,setVarHOLFinite,domain] using arena
  have result := rlpValidation_list_continuation_invariant entered output position stop header payload scratch frame frames
    ((localFrame _ (by decide)).trans positionLocal) ((localFrame _ (by decide)).trans stopLocal)
    ((localFrame _ (by decide)).trans topLocal) atHeader valid enteredStack intervals inputBound
    atScratch atFrame (readyCode.trans code) (by change 2 ≤ ready.clock; omega) orderedFrame framePositive arenaEntered tail
  dsimp only at result ⊢
  rw [restored]
  refine ⟨?_,?_,?_,result.2.2.2.1,result.2.2.2.2.1,result.2.2.2.2.2.1,?_⟩
  · rw [restore_other_local _ _ (ofString "pos") _ (by decide)]
    exact result.1
  · rw [restore_other_local _ _ (ofString "end") _ (by decide)]
    exact result.2.1
  · rw [restore_other_local _ _ (ofString "top") _ (by decide)]
    exact result.2.2.1
  · have clock := result.2.2.2.2.2.2
    change output.clock = ready.clock - 1 at clock
    change state.clock ≤ output.clock + 13
    omega

#print axioms rlpValidation_parse_list_invariant
end InitECandidate.Runtime
