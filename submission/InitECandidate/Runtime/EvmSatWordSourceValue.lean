import InitECandidate.Runtime.U256ZeroFundingValue
import InitECandidate.Runtime.OriginalRuntimeCode
import InitECandidate.Runtime.FrameNewSource
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

def evmSatWord (a b c d : BitVec 64) : BitVec 64 :=
 if (b|||c)|||d=0#64 then a else 18446744073709551615#64

def evmSatWordCondition : ExpHOL 64:=.cmp .notEqual
 (.op .or [.rfield 1 (.var .local (ofString "v")),.rfield 2 (.var .local (ofString "v")),.rfield 3 (.var .local (ofString "v"))]) (.const 0)
theorem source_evm_sat_word_body : sourceFunctionBody Guest.guestFn_sat_word=
 .seq (.ite evmSatWordCondition (.return (.const 18446744073709551615)) .skip)
  (.return (.rfield 0 (.var .local (ofString "v")))) := by cbv
/-- The exact original saturation helper on an actual word-valued U256.
All effects are source return cleanup; no semantic callee oracle. -/
theorem evaluate_source_evm_sat_word {F : Type} (s : PanSemStateFiniteExact 64 F)
 (a b c d : BitVec 64)
 (atValue : s.locals.lookup (ofString "v")=some (fundingU256 a b c d)) :
 evaluateHOLFiniteState s (sourceFunctionBody Guest.guestFn_sat_word)=
  (some (.returned (.val (.word (evmSatWord a b c d)))),emptyLocalsHOLFinite s) := by
 have orDef (x y : BitVec 64) : OrOp.or x y=x|||y :=rfl
 have condition : @evalHOLExact 64 F _ s.toExact (fun address=>Classical.propDecidable (s.memaddrs address)) evmSatWordCondition=
  some (.val (.word (if (b|||c)|||d=0#64 then 0 else 1))) := by
  by_cases bz : b=0#64 <;> by_cases cz : c=0#64 <;> by_cases dz : d=0#64
  all_goals simp [evmSatWordCondition,evalHOLExact,evalListHOLExact,atValue,fundingU256,wordOpHOL,wordOp,valueIsWord,valueWord,orDef,Flapjack.Compiler.Encoders.Asm.wordCmpHOL,bz,cz,dz]
 rw [source_evm_sat_word_body,evaluateHOLFiniteState_seq_line780,evaluateHOLFiniteState_ite,condition]
 by_cases zero : (b|||c)|||d=0#64
 · simp [zero,evmSatWord,evaluateHOLFiniteState_skip,evaluateHOLFiniteState_return,evalHOLExact,atValue,fundingU256,shapeOfHOLExact]
 · simp [zero,evmSatWord,evaluateHOLFiniteState_return,evalHOLExact,shapeOfHOLExact]
#print axioms source_evm_sat_word_body
#print axioms evaluate_source_evm_sat_word
end InitECandidate.Runtime
