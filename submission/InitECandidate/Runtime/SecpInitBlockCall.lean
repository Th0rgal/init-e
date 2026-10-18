import InitECandidate.Runtime.SecpInitBlockSuccess
import InitECandidate.Runtime.PanWordStruct4Lookup
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- A call of the actual secp_accel_init_block writes its eight words at
base+64..base+120, costs one tick and changes nothing else. -/
theorem evaluate_secpAccelInitBlock_call {F : Type} (state : PanSemStateFiniteExact 64 F)
    (arguments : List (ExpHOL 64)) (base m0 m1 m2 m3 : BitVec 64)
    (code : state.code = originalRuntimeCode)
    (args : evalListHOLFinite state (h := fun a => Classical.propDecidable (state.memaddrs a)) arguments =
      some [.val (.word base),.rStruct [.val (.word m0),.val (.word m1),.val (.word m2),.val (.word m3)]])
    (domain : ∀ cell ∈ secpBlockCells m0 m1 m2 m3, state.memaddrs (base + cell.1))
    (nonzero : state.clock ≠ 0) :
    evaluateHOLFiniteState state (.call (some (none,none)) (ofString "secp_accel_init_block") arguments) =
      (none,{state with clock := state.clock - 1, memory := memWrites state.memory base (secpBlockCells m0 m1 m2 m3)}) := by
  have lookup := pan_word_struct4_lookup state.code.lookup (ofString "secp_accel_init_block")
    (ofString "base") (ofString "modulus") (sourceFunctionBody Guest.guestFn_secp_accel_init_block) .one
    base m0 m1 m2 m3 (by decide)
    (by rw [code]; exact originalRuntimeCode_secpAccelInitBlock_lookup)
  let callee := (HolFiniteMapExact.empty.update (ofString "base",ValueHOL.val (.word base))).update
    (ofString "modulus",ValueHOL.rStruct [.val (.word m0),.val (.word m1),.val (.word m2),.val (.word m3)])
  let entry := callEntryStateHOLFinite state callee
  have names : ofString "modulus" ≠ ofString "base" := by decide
  have body := evaluate_secpAccelInitBlock_body entry base m0 m1 m2 m3
    (by simp [entry,callee,callEntryStateHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,names])
    (by simp [entry,callee,callEntryStateHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE])
    domain
  rw [evaluateHOLFiniteState_call_return_caller_locals state none (ofString "secp_accel_init_block") arguments _
    (sourceFunctionBody Guest.guestFn_secp_accel_init_block) callee .one (.val (.word 0)) _
    args lookup nonzero body (by simp [shapeOfHOLExact,shapeEqHOL])]
  rfl

#print axioms evaluate_secpAccelInitBlock_call
end InitECandidate.Runtime
