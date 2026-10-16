import InitECandidate.Runtime.GasRefill
import InitECandidate.Runtime.OriginalFrameErrorCode
import InitECandidate.Runtime.PanNoArgsLookup
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

noncomputable def gasRefillSourcePost {F : Type} (state : PanSemStateFiniteExact 64 F)
    (frame msg left spilled gas : BitVec 64) :=
  let entered := setVarHOLFinite (ofString "msg") (.val (.word msg)) state
  let bodyPost := refillPost entered frame left spilled gas
  {bodyPost with locals := (HolFiniteMapExact.resVarEq bodyPost.locals
    (ofString "msg",state.locals.lookup (ofString "msg")))}

noncomputable def gasRefillCallPost {F : Type} (state : PanSemStateFiniteExact 64 F)
    (frame left spilled gas : BitVec 64) :=
  sourceWriteWord (sourceWriteWord (sourceWriteWord {state with clock := state.clock - 1}
    (frame + 64) (left + spilled)) (frame + 72) gas) (frame + 192) 0

/-- Exact refill execution at the original call boundary, including all three
stores and restoration of caller locals. No global gas-budget premise is needed. -/
theorem evaluate_gasRefill_call {F : Type} (state : PanSemStateFiniteExact 64 F)
    (frame msg gas left spilled : BitVec 64)
    (code : state.code = originalRuntimeCode) (clock : state.clock ≠ 0)
    (frameGlobal : state.globals.lookup (ofString "ev") = some (.val (.word frame)))
    (leftDomain : state.memaddrs (frame + 64)) (spillDomain : state.memaddrs (frame + 192))
    (stateDomain : state.memaddrs (frame + 72)) (pointerDomain : state.memaddrs (frame + 112))
    (msgDomain : state.memaddrs (msg + 48))
    (leftMemory : state.memory (frame + 64) = .word left)
    (spillMemory : state.memory (frame + 192) = .word spilled)
    (pointerMemory : state.memory (frame + 112) = .word msg)
    (msgMemory : state.memory (msg + 48) = .word gas) (separate : msg + 48 ≠ frame + 64) :
    evaluateHOLFiniteState state (.call (some (none,none)) (ofString "refill_frame_state_gas") []) =
      (none,gasRefillCallPost state frame left spilled gas) := by
  classical
  let entry := callEntryStateHOLFinite state HolFiniteMapExact.empty
  let entered := setVarHOLFinite (ofString "msg") (.val (.word msg)) entry
  have msgLocal : entered.locals.lookup (ofString "msg") = some (.val (.word msg)) := by
    simp [entered,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]
  have stores := evaluate_refillStores entered frame msg gas left spilled frameGlobal msgLocal
    leftDomain spillDomain stateDomain msgDomain leftMemory spillMemory msgMemory separate
  have body : evaluateHOLFiniteState entry (sourceFunctionBody Guest.guestFn_refill_frame_state_gas) =
      (some (.returned (.val (.word 0))),gasRefillSourcePost entry frame msg left spilled gas) := by
    rw [source_gasRefill_body,evaluateHOLFiniteState_dec_total]
    dsimp only
    rw [eval_fundingLoad entry frame 112 msg frameGlobal pointerDomain pointerMemory]
    simp only [shapeOfHOLExact,shapeEqHOL]
    change (let output := evaluateHOLFiniteState entered refillStores;
      (output.1,{output.2 with locals := (HolFiniteMapExact.resVarEq output.2.locals
        (ofString "msg",entry.locals.lookup (ofString "msg")))})) = _
    rw [stores]
    rfl
  have installed : state.code.lookup (ofString "refill_frame_state_gas") =
      some ([],sourceFunctionBody Guest.guestFn_refill_frame_state_gas,.one) := by
    rw [code]; exact originalRuntimeCode_refillFrameStateGas_lookup
  have lookup := pan_no_args_lookup state.code.lookup (ofString "refill_frame_state_gas")
    (sourceFunctionBody Guest.guestFn_refill_frame_state_gas) installed
  have call := evaluateHOLFiniteState_call_return_caller_locals state none (ofString "refill_frame_state_gas") [] []
    (sourceFunctionBody Guest.guestFn_refill_frame_state_gas) HolFiniteMapExact.empty .one (.val (.word 0))
    (gasRefillSourcePost entry frame msg left spilled gas)
    (by simp [evalListHOLFinite,evalListHOLExact]) lookup clock body (by simp [shapeOfHOLExact,shapeEqHOL])
  exact call

theorem gasRefillCallPost_funding {F : Type} (state : PanSemStateFiniteExact 64 F)
    (frame gas : BitVec 64) (funding : GasFunding) (memory : HasGasFunding state frame funding) :
    HasGasFunding (gasRefillCallPost state frame funding.left funding.spilled gas)
      frame (funding.repay funding.spilled) := by
  exact refillPost_funding {state with clock := state.clock - 1} frame gas funding memory

theorem gasRefillCallPost_memory_preserved {F : Type} (state : PanSemStateFiniteExact 64 F)
    (frame left spilled gas address : BitVec 64)
    (notLeft : address ≠ frame + 64) (notState : address ≠ frame + 72)
    (notSpill : address ≠ frame + 192) :
    (gasRefillCallPost state frame left spilled gas).memory address = state.memory address := by
  unfold gasRefillCallPost sourceWriteWord
  dsimp only
  rw [if_neg notSpill,if_neg notState,if_neg notLeft]

#print axioms gasRefillCallPost_funding
#print axioms gasRefillCallPost_memory_preserved
#print axioms evaluate_gasRefill_call
end InitECandidate.Runtime
