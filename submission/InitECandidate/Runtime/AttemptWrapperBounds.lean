import InitECandidate.Runtime.AttemptWrapperGenericBound
import InitECandidate.Runtime.OriginalAttemptWrapperCode
namespace InitECandidate.Runtime
open InitE Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem runBounded_attempt_l1 {F : Type} (s : PanSemStateFiniteExact 64 F) (si : BitVec 64) (cost : Nat)
    (atSi : s.locals.lookup (ofString "si")=some (.val (.word si)))
    (code : s.code=originalRuntimeCode) (budget : cost+1≤s.clock)
    (bounded : RunBounded (attemptEntry s si 1) (sourceFunctionBody Guest.guestFn_run_attempt) cost) :
    RunBounded s (sourceFunctionBody Guest.guestFn_attempt_l1) (cost+1) := by
  rw [source_attempt_l1_body]
  have inner : RunBounded (attemptEntry s si 1) (sourceFunctionBody Guest.guestFn_run_attempt) (cost+0) := by
    simpa only [Nat.add_zero] using bounded
  have result := runBounded_attempt_layer s si (ofString "run_attempt") (ofString "BlockErr") 1#64
    (sourceFunctionBody Guest.guestFn_run_attempt) (cost+0) atSi originalRuntimeCode_RunAttempt_lookup code (by omega) inner
  simpa only [Nat.add_assoc] using result
#print axioms runBounded_attempt_l1
theorem runBounded_attempt_l2 {F : Type} (s : PanSemStateFiniteExact 64 F) (si : BitVec 64) (cost : Nat)
    (atSi : s.locals.lookup (ofString "si")=some (.val (.word si)))
    (code : s.code=originalRuntimeCode) (budget : cost+2≤s.clock)
    (bounded : RunBounded (attemptEntry s si 2) (sourceFunctionBody Guest.guestFn_run_attempt) cost) :
    RunBounded s (sourceFunctionBody Guest.guestFn_attempt_l2) (cost+2) := by
  rw [source_attempt_l2_body]
  have inner : RunBounded (attemptEntry s si 1) (sourceFunctionBody Guest.guestFn_attempt_l1) (cost+1) := by
    apply runBounded_attempt_l1 (attemptEntry s si 1) si cost (attemptEntry_si s si 1) code (by change cost+1≤s.clock-1;omega)
    simpa only [attemptEntry_nested] using bounded
  have result := runBounded_attempt_layer s si (ofString "attempt_l1") (ofString "HdrErr") 2#64
    (sourceFunctionBody Guest.guestFn_attempt_l1) (cost+1) atSi originalRuntimeCode_AttemptL1_lookup code (by omega) inner
  simpa only [Nat.add_assoc] using result
#print axioms runBounded_attempt_l2
theorem runBounded_attempt_l3 {F : Type} (s : PanSemStateFiniteExact 64 F) (si : BitVec 64) (cost : Nat)
    (atSi : s.locals.lookup (ofString "si")=some (.val (.word si)))
    (code : s.code=originalRuntimeCode) (budget : cost+3≤s.clock)
    (bounded : RunBounded (attemptEntry s si 3) (sourceFunctionBody Guest.guestFn_run_attempt) cost) :
    RunBounded s (sourceFunctionBody Guest.guestFn_attempt_l3) (cost+3) := by
  rw [source_attempt_l3_body]
  have inner : RunBounded (attemptEntry s si 1) (sourceFunctionBody Guest.guestFn_attempt_l2) (cost+2) := by
    apply runBounded_attempt_l2 (attemptEntry s si 1) si cost (attemptEntry_si s si 1) code (by change cost+2≤s.clock-1;omega)
    simpa only [attemptEntry_nested] using bounded
  have result := runBounded_attempt_layer s si (ofString "attempt_l2") (ofString "RlpErr") 3#64
    (sourceFunctionBody Guest.guestFn_attempt_l2) (cost+2) atSi originalRuntimeCode_AttemptL2_lookup code (by omega) inner
  simpa only [Nat.add_assoc] using result
#print axioms runBounded_attempt_l3
theorem runBounded_attempt_l4 {F : Type} (s : PanSemStateFiniteExact 64 F) (si : BitVec 64) (cost : Nat)
    (atSi : s.locals.lookup (ofString "si")=some (.val (.word si)))
    (code : s.code=originalRuntimeCode) (budget : cost+4≤s.clock)
    (bounded : RunBounded (attemptEntry s si 4) (sourceFunctionBody Guest.guestFn_run_attempt) cost) :
    RunBounded s (sourceFunctionBody Guest.guestFn_attempt_l4) (cost+4) := by
  rw [source_attempt_l4_body]
  have inner : RunBounded (attemptEntry s si 1) (sourceFunctionBody Guest.guestFn_attempt_l3) (cost+3) := by
    apply runBounded_attempt_l3 (attemptEntry s si 1) si cost (attemptEntry_si s si 1) code (by change cost+3≤s.clock-1;omega)
    simpa only [attemptEntry_nested] using bounded
  have result := runBounded_attempt_layer s si (ofString "attempt_l3") (ofString "MptErr") 4#64
    (sourceFunctionBody Guest.guestFn_attempt_l3) (cost+3) atSi originalRuntimeCode_AttemptL3_lookup code (by omega) inner
  simpa only [Nat.add_assoc] using result
#print axioms runBounded_attempt_l4
theorem runBounded_attempt_l5 {F : Type} (s : PanSemStateFiniteExact 64 F) (si : BitVec 64) (cost : Nat)
    (atSi : s.locals.lookup (ofString "si")=some (.val (.word si)))
    (code : s.code=originalRuntimeCode) (budget : cost+5≤s.clock)
    (bounded : RunBounded (attemptEntry s si 5) (sourceFunctionBody Guest.guestFn_run_attempt) cost) :
    RunBounded s (sourceFunctionBody Guest.guestFn_attempt_l5) (cost+5) := by
  rw [source_attempt_l5_body]
  have inner : RunBounded (attemptEntry s si 1) (sourceFunctionBody Guest.guestFn_attempt_l4) (cost+4) := by
    apply runBounded_attempt_l4 (attemptEntry s si 1) si cost (attemptEntry_si s si 1) code (by change cost+4≤s.clock-1;omega)
    simpa only [attemptEntry_nested] using bounded
  have result := runBounded_attempt_layer s si (ofString "attempt_l4") (ofString "StateErr") 5#64
    (sourceFunctionBody Guest.guestFn_attempt_l4) (cost+4) atSi originalRuntimeCode_AttemptL4_lookup code (by omega) inner
  simpa only [Nat.add_assoc] using result
#print axioms runBounded_attempt_l5
theorem runBounded_attempt_l6 {F : Type} (s : PanSemStateFiniteExact 64 F) (si : BitVec 64) (cost : Nat)
    (atSi : s.locals.lookup (ofString "si")=some (.val (.word si)))
    (code : s.code=originalRuntimeCode) (budget : cost+6≤s.clock)
    (bounded : RunBounded (attemptEntry s si 6) (sourceFunctionBody Guest.guestFn_run_attempt) cost) :
    RunBounded s (sourceFunctionBody Guest.guestFn_attempt_l6) (cost+6) := by
  rw [source_attempt_l6_body]
  have inner : RunBounded (attemptEntry s si 1) (sourceFunctionBody Guest.guestFn_attempt_l5) (cost+5) := by
    apply runBounded_attempt_l5 (attemptEntry s si 1) si cost (attemptEntry_si s si 1) code (by change cost+5≤s.clock-1;omega)
    simpa only [attemptEntry_nested] using bounded
  have result := runBounded_attempt_layer s si (ofString "attempt_l5") (ofString "TxErr") 6#64
    (sourceFunctionBody Guest.guestFn_attempt_l5) (cost+5) atSi originalRuntimeCode_AttemptL5_lookup code (by omega) inner
  simpa only [Nat.add_assoc] using result
#print axioms runBounded_attempt_l6
theorem runBounded_attempt_l7 {F : Type} (s : PanSemStateFiniteExact 64 F) (si : BitVec 64) (cost : Nat)
    (atSi : s.locals.lookup (ofString "si")=some (.val (.word si)))
    (code : s.code=originalRuntimeCode) (budget : cost+7≤s.clock)
    (bounded : RunBounded (attemptEntry s si 7) (sourceFunctionBody Guest.guestFn_run_attempt) cost) :
    RunBounded s (sourceFunctionBody Guest.guestFn_attempt_l7) (cost+7) := by
  rw [source_attempt_l7_body]
  have inner : RunBounded (attemptEntry s si 1) (sourceFunctionBody Guest.guestFn_attempt_l6) (cost+6) := by
    apply runBounded_attempt_l6 (attemptEntry s si 1) si cost (attemptEntry_si s si 1) code (by change cost+6≤s.clock-1;omega)
    simpa only [attemptEntry_nested] using bounded
  have result := runBounded_attempt_layer s si (ofString "attempt_l6") (ofString "EvmErr") 7#64
    (sourceFunctionBody Guest.guestFn_attempt_l6) (cost+6) atSi originalRuntimeCode_AttemptL6_lookup code (by omega) inner
  simpa only [Nat.add_assoc] using result
#print axioms runBounded_attempt_l7
/-- Full original exception ladder, including verify's Fail handler, costs
at most eight ticks beyond actual run_attempt. The premise is exactly its
callee entry; initial memory/globals/domain/code are unchanged there. -/
theorem runBounded_verify_attempt_wrapper {F : Type} (s : PanSemStateFiniteExact 64 F)
    (si : BitVec 64) (cost : Nat)
    (atSi : s.locals.lookup (ofString "si")=some (.val (.word si)))
    (code : s.code=originalRuntimeCode) (budget : cost+8≤s.clock)
    (bounded : RunBounded (attemptEntry s si 8) (sourceFunctionBody Guest.guestFn_run_attempt) cost) :
    RunBounded s (sourceFunctionBody Guest.guestFn_verify_stateless_new_payload) (cost+8) := by
  rw [source_verify_attempt_body]
  unfold verifyAttemptBody
  apply RunBounded.decConst s (ofString "e") (0#64)
  let first:=setVarHOLFinite (ofString "e") (.val (.word (0#64))) s
  apply RunBounded.decConst first (ofString "ok") (1#64)
  let entered:=setVarHOLFinite (ofString "ok") (.val (.word (1#64))) first
  have inner : RunBounded (attemptEntry entered si 1) (sourceFunctionBody Guest.guestFn_attempt_l7) (cost+7) := by
    apply runBounded_attempt_l7 (attemptEntry entered si 1) si cost (attemptEntry_si entered si 1) code
      (by change cost+7≤s.clock-1;omega)
    simpa only [attemptEntry_nested,entered,first,attemptEntry,setVarHOLFinite,Nat.sub_sub] using bounded
  have result := runBounded_attempt_call_return entered si (ofString "attempt_l7") (ofString "Fail")
    (sourceFunctionBody Guest.guestFn_attempt_l7) verifyAttemptHandler (.var .local (ofString "ok")) (cost+7)
    (by simpa (config := {decide := true}) [entered,first,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE] using atSi)
    originalRuntimeCode_AttemptL7_lookup code (by change cost+7+1≤s.clock;omega) inner verify_attempt_handler_bounded
  simpa only [Nat.add_assoc] using result
#print axioms runBounded_verify_attempt_wrapper
#print axioms runBounded_attempt_layer
end InitECandidate.Runtime
