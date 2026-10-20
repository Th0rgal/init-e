import InitECandidate.Runtime.AttemptWrapperBounds
import InitECandidate.Runtime.MainAttemptEntryPayloadReach
import InitECandidate.Runtime.MainNormalSuffixNoDomainBound
/-! The actual `mainAt 23` verify call, reduced to the normal output suffix. -/
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

/-- The real `main` statement 23: the actual verify call, one-argument, result in `succ`, continuing
with the normal output serialization at `mainAt 24`. -/
theorem source_main_verify_call :
    mainAt 23 = (.decCall (ofString "succ") .one (ofString "verify_stateless_new_payload")
      [.var .local (ofString "si")] (mainAt 24) : ProgHOL 64) := by
  simp only [mainAt,statelessNext,sourceFunctionBody,
    InitECandidate.Proofs.FrontendCodecComputation.declToHOL_eq]
  rfl
#print axioms source_main_verify_call

/-- **The actual `mainAt 23` verify call is bounded by the run_attempt body cost plus eight wrapper
ticks, one call tick and the 65-tick normal suffix.**  Premises: the typed `out`/`root`/`si` locals of
the ORIGINAL caller state, the installed original code, the clock, the actual run_attempt body bound at
the depth-nine wrapper entry, and the fact that the actual verify body returns a word normally.
`succ` is NOT assumed: it is the call's own result binding, restored by the real `decCall` semantics. -/
theorem runBounded_main_verify_normal {F : Type} (s : PanSemStateFiniteExact 64 F)
    (out root si word : BitVec 64) (runCost : Nat) (post : PanSemStateFiniteExact 64 F)
    (atOut : s.locals.lookup (ofString "out")=some (.val (.word out)))
    (atRoot : s.locals.lookup (ofString "root")=some (.val (.word root)))
    (atSi : s.locals.lookup (ofString "si")=some (.val (.word si)))
    (code : s.code=originalRuntimeCode) (budget : runCost+8+1+65≤s.clock)
    (bounded : RunBounded (attemptEntry s si 9) (sourceFunctionBody Guest.guestFn_run_attempt) runCost)
    (verifyRun : evaluateHOLFiniteState (attemptEntry s si 1)
      (sourceFunctionBody Guest.guestFn_verify_stateless_new_payload)=
      (some (.returned (.val (.word word))),post)) :
    RunBounded s (mainAt 23) (runCost+8+1+65) := by
  have args : evalListHOLFinite s (h:=fun a=>Classical.propDecidable (s.memaddrs a))
      [.var .local (ofString "si")]=some [.val (.word si)] := by
    simp [evalListHOLFinite,evalListHOLExact,evalHOLExact,atSi]
  have lookup := pan_single_word_lookup s.code.lookup (ofString "verify_stateless_new_payload")
    (ofString "si") (sourceFunctionBody Guest.guestFn_verify_stateless_new_payload) si
    (by rw [code];exact originalRuntimeCode_VerifyAttempt_lookup)
  have nested : attemptEntry (attemptEntry s si 1) si 8 = attemptEntry s si 9 := by
    rw [attemptEntry_nested]
  have inner : RunBounded (attemptEntry (attemptEntry s si 1) si 8)
      (sourceFunctionBody Guest.guestFn_run_attempt) runCost := by
    rw [nested]; exact bounded
  have wrapperBounded : RunBounded (attemptEntry s si 1)
      (sourceFunctionBody Guest.guestFn_verify_stateless_new_payload) (runCost+8) :=
    runBounded_verify_attempt_wrapper (attemptEntry s si 1) si runCost (attemptEntry_si s si 1)
      (by simpa [attemptEntry] using code) (by change runCost+8≤s.clock-1;omega) inner
  unfold RunBounded at wrapperBounded
  rw [verifyRun] at wrapperBounded
  have entryClock : s.clock-1≤post.clock+(runCost+8) := by simpa [attemptEntry] using wrapperBounded.1
  have postClock : post.clock≤s.clock-1 := by simpa [attemptEntry] using wrapperBounded.2.1
  have postCode : post.code=originalRuntimeCode := by
    have metadata := evaluateHOLFiniteState_metadata (attemptEntry s si 1)
      (sourceFunctionBody Guest.guestFn_verify_stateless_new_payload)
    rw [verifyRun] at metadata
    exact metadata.1.trans code
  have minEq : (if s.clock-1<post.clock then s.clock-1 else post.clock)=post.clock := by
    split
    · omega
    · rfl
  unfold RunBounded
  rw [source_main_verify_call, evaluateHOLFiniteState_decCall_total, args]
  dsimp only
  rw [lookup]
  dsimp only
  rw [if_neg (by omega : ¬ s.clock=0)]
  rw [show s.callEntryStateHOLFinite (HolFiniteMapExact.empty.update
      (ofString "si", .val (.word si))) = attemptEntry s si 1 from rfl]
  rw [verifyRun]
  dsimp only
  rw [if_pos (by simp [shapeEqHOL,shapeOfHOLExact] : (shapeEqHOL (shapeOfHOLExact (.val (.word word))) .one &&
      shapeEqHOL (shapeOfHOLExact (.val (.word word))) .one)=true)]
  dsimp only
  generalize hcontState : (setVarHOLFinite (ofString "succ") (.val (.word word))
      { (fixClockHOLFinite (attemptEntry s si 1)
          ((some (PanSemResultExact.returned (.val (.word word))) : Option (PanSemResultExact 64)),
            post)).2 with locals := s.locals }) = contState
  have suffix : RunBounded contState (mainAt 24) 65 := by
    rw [← hcontState]
    refine runBounded_main_normal_suffix_no_domain _ out root word si ?_ ?_ ?_ ?_ ?_ ?_
    · simpa (config := {decide := true}) [setVarHOLFinite,fixClockHOLFinite,
        HolFiniteMapExact.lookup_update,FUPDATE] using atOut
    · simpa (config := {decide := true}) [setVarHOLFinite,fixClockHOLFinite,
        HolFiniteMapExact.lookup_update,FUPDATE] using atRoot
    · simp (config := {decide := true}) [setVarHOLFinite,fixClockHOLFinite,
        HolFiniteMapExact.lookup_update,FUPDATE]
    · simpa (config := {decide := true}) [setVarHOLFinite,fixClockHOLFinite,
        HolFiniteMapExact.lookup_update,FUPDATE] using atSi
    · simp only [setVarHOLFinite,fixClockHOLFinite]
      exact postCode
    · simp only [setVarHOLFinite,fixClockHOLFinite,attemptEntry]
      by_cases h : s.clock-1<post.clock <;> simp [h] at * <;> omega
  cases contRun : evaluateHOLFiniteState contState (mainAt 24) with
  | mk contResult contPost =>
    unfold RunBounded at suffix
    rw [contRun] at suffix
    have clockVal : contState.clock=post.clock := by
      rw [← hcontState]
      simp only [setVarHOLFinite,fixClockHOLFinite,attemptEntry]
      by_cases h : s.clock-1<post.clock
      · omega
      · simp [h]
    rw [clockVal] at suffix
    dsimp only at suffix ⊢
    exact ⟨by omega,by omega,suffix.2.2⟩
#print axioms runBounded_main_verify_normal
end InitECandidate.Runtime
