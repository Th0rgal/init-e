import InitECandidate.Runtime.MainVerifyNormalBound
import InitECandidate.Runtime.MainNormalSuffixValueBound
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000
/-- Complete actual main verification/output suffix from one actual run_attempt
body bound. Every return shape, error, exception and FFI outcome is included;
no successful verify return, output-memory frame or restored-locals premise is assumed. -/
theorem runBounded_main_verify_all_outcomes {F : Type} (s : PanSemStateFiniteExact 64 F)
 (output root si : BitVec 64) (runCost : Nat)
 (atOutput : s.locals.lookup (ofString "out")=some (.val (.word output)))
 (atRoot : s.locals.lookup (ofString "root")=some (.val (.word root)))
 (atSi : s.locals.lookup (ofString "si")=some (.val (.word si)))
 (code : s.code=originalRuntimeCode) (budget : runCost+8+1+65≤s.clock)
 (bounded : RunBounded (attemptEntry s si 9) (sourceFunctionBody Guest.guestFn_run_attempt) runCost) :
 RunBounded s (mainAt 23) (runCost+8+1+65) := by
 have args : evalListHOLFinite s (h:=fun a=>Classical.propDecidable (s.memaddrs a)) [.var .local (ofString "si")]=
  some [.val (.word si)] := by
  rw [evalListHOLFinite_eq_toExact];simp [evalListHOLExact,evalHOLExact,atSi]
 have lookup:=pan_single_word_lookup s.code.lookup (ofString "verify_stateless_new_payload") (ofString "si")
  (sourceFunctionBody Guest.guestFn_verify_stateless_new_payload) si
  (by rw [code];exact originalRuntimeCode_VerifyAttempt_lookup)
 have inner : RunBounded (attemptEntry (attemptEntry s si 1) si 8)
  (sourceFunctionBody Guest.guestFn_run_attempt) runCost := by
  rw [attemptEntry_nested];exact bounded
 have wrapperBounded:=runBounded_verify_attempt_wrapper (attemptEntry s si 1) si runCost (attemptEntry_si s si 1)
  code (by change runCost+8≤s.clock-1;omega) inner
 rw [source_main_verify_call]
 apply RunBounded.decCall (bodyCost:=runCost+8) (tailCost:=65) args budget
 intro body callee returnShape found
 rw [lookup] at found
 obtain ⟨rfl,rfl,rfl⟩:=Option.some.inj found |>.symm
 refine ⟨wrapperBounded,?_⟩
 intro value post run ticks
 change evaluateHOLFiniteState (attemptEntry s si 1) (sourceFunctionBody Guest.guestFn_verify_stateless_new_payload)=
  (some (.returned value),post) at run
 have metadata:=evaluateHOLFiniteState_metadata (attemptEntry s si 1)
  (sourceFunctionBody Guest.guestFn_verify_stateless_new_payload)
 rw [run] at metadata
 apply runBounded_main_normal_suffix_any_success _ output root si value
 · simpa (config:={decide:=true}) [setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE] using atOutput
 · simpa (config:={decide:=true}) [setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE] using atRoot
 · simp [setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]
 · simpa (config:={decide:=true}) [setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE] using atSi
 · exact metadata.1.trans code
 · exact ticks
#print axioms runBounded_main_verify_all_outcomes
end InitECandidate.Runtime
