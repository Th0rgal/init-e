import InitECandidate.Runtime.DecodeRequestsSource
import InitECandidate.Runtime.SszBodyFrames
import InitECandidate.Runtime.PanFourWordLookup
import InitECandidate.Runtime.CallBodyClockNoTimeout
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

def reqCheckLocals (offsets length : BitVec 64) : HolFiniteMapExact MlS (ValueHOL 64) :=
  (((HolFiniteMapExact.empty.update (ofString "offs",.val (.word offsets))).update
    (ofString "n",.val (.word 5))).update (ofString "fixed",.val (.word 20))).update
    (ofString "len",.val (.word length))

theorem reqCheck_args {σ : Type} (s : PanSemStateFiniteExact 64 σ) (offsets length : BitVec 64)
    (hg : s.globals.lookup (ofString "ssz_offs") = some (.val (.word offsets)))
    (hl : s.locals.lookup (ofString "len") = some (.val (.word length))) :
    evalListHOLFinite s (h := fun address => Classical.propDecidable (s.memaddrs address))
      [reqGlobal, .const 5, .const 20, sszLocal "len"] =
      some [.val (.word offsets), .val (.word 5), .val (.word 20), .val (.word length)] := by
  simp [reqGlobal, sszLocal, evalListHOLFinite, evalListHOLExact, evalHOLExact, hg, hl]

theorem reqCheck_lookup {σ : Type} (s : PanSemStateFiniteExact 64 σ) (offsets length : BitVec 64)
    (code : s.code = originalRuntimeCode) :
    lookupCodeHOLFinite s.code.lookup (ofString "ssz_check_offsets")
      [.val (.word offsets), .val (.word 5), .val (.word 20), .val (.word length)] =
      some (sourceFunctionBody Guest.guestFn_ssz_check_offsets, reqCheckLocals offsets length, .one) :=
  pan_four_word_lookup s.code.lookup (ofString "ssz_check_offsets") (ofString "offs") (ofString "n")
    (ofString "fixed") (ofString "len") _ offsets 5 20 length (by decide_cbv) (by decide_cbv) (by decide_cbv)
    (by decide_cbv) (by decide_cbv) (by decide_cbv) (by rw [code]; exact originalRuntimeCode_sszCheckOffsets_lookup)

theorem reqCheck_entry_lookups {σ : Type} (s : PanSemStateFiniteExact 64 σ) (offsets length : BitVec 64) :
    let entry := callEntryStateHOLFinite s (reqCheckLocals offsets length)
    entry.locals.lookup (ofString "offs") = some (.val (.word offsets)) ∧
    entry.locals.lookup (ofString "n") = some (.val (.word 5)) ∧
    entry.locals.lookup (ofString "fixed") = some (.val (.word 20)) ∧
    entry.locals.lookup (ofString "len") = some (.val (.word length)) := by
  have a : ofString "n" ≠ ofString "offs" := by decide_cbv
  have b : ofString "fixed" ≠ ofString "offs" := by decide_cbv
  have c : ofString "len" ≠ ofString "offs" := by decide_cbv
  have d : ofString "fixed" ≠ ofString "n" := by decide_cbv
  have e : ofString "len" ≠ ofString "n" := by decide_cbv
  have f : ofString "len" ≠ ofString "fixed" := by decide_cbv
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
    simp [reqCheckLocals, callEntryStateHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, a, b, c, d, e, f]

/-- The actual offset-check call costs at most 12 ticks and does not time out with that clock. -/
theorem reqCheck_bounded {σ : Type} (s : PanSemStateFiniteExact 64 σ) (offsets length : BitVec 64)
    (hg : s.globals.lookup (ofString "ssz_offs") = some (.val (.word offsets)))
    (hl : s.locals.lookup (ofString "len") = some (.val (.word length)))
    (code : s.code = originalRuntimeCode) (enough : 12 ≤ s.clock) :
    s.clock ≤ (evaluateHOLFiniteState s reqCheck).2.clock + 12 ∧
      (evaluateHOLFiniteState s reqCheck).2.clock ≤ s.clock ∧
      (evaluateHOLFiniteState s reqCheck).1 ≠ some .timeOut := by
  obtain ⟨e1, e2, e3, e4⟩ := reqCheck_entry_lookups s offsets length
  have body := evaluate_sszCheckOffsets_body (callEntryStateHOLFinite s (reqCheckLocals offsets length))
    offsets 5 20 length code e1 e2 e3 e4 (by decide)
  cases run : evaluateHOLFiniteState (callEntryStateHOLFinite s (reqCheckLocals offsets length))
      (sourceFunctionBody Guest.guestFn_ssz_check_offsets) with
  | mk result post =>
    rw [run] at body
    dsimp only at body
    obtain ⟨b1, b2, b3, _, _⟩ := body
    have entryClock : (callEntryStateHOLFinite s (reqCheckLocals offsets length)).clock = s.clock - 1 := rfl
    rw [entryClock] at b1 b2 b3
    have output := evaluate_call_body_clock_no_timeout s post (ofString "ssz_check_offsets") none _ _
      _ _ .one result (reqCheck_args s offsets length hg hl) (reqCheck_lookup s offsets length code) (by omega) run
      (b3 (by simp; omega))
    unfold reqCheck
    dsimp only at output
    rw [output.2]
    exact ⟨by simp at b1; omega, by omega, output.1⟩

/-- A normally completed offset-check call: the actual body returned 0 with the
offset contract, and caller locals, memory, globals, domain and code are kept. -/
theorem reqCheck_normal {σ : Type} (s post : PanSemStateFiniteExact 64 σ) (offsets length : BitVec 64)
    (hg : s.globals.lookup (ofString "ssz_offs") = some (.val (.word offsets)))
    (hl : s.locals.lookup (ofString "len") = some (.val (.word length)))
    (code : s.code = originalRuntimeCode)
    (run : evaluateHOLFiniteState s reqCheck = (none, post)) :
    SszCheckOffsetsReturned (callEntryStateHOLFinite s (reqCheckLocals offsets length)) offsets 5 20 length (.val (.word 0)) ∧
      post.locals = s.locals ∧ post.memory = s.memory ∧ post.globals = s.globals ∧ post.memaddrs = s.memaddrs ∧
      post.code = s.code := by
  obtain ⟨e1, e2, e3, e4⟩ := reqCheck_entry_lookups s offsets length
  have args := reqCheck_args s offsets length hg hl
  have lookup := reqCheck_lookup s offsets length code
  unfold reqCheck at run
  rw [evaluateHOLFiniteState_call, args] at run
  dsimp only at run
  rw [lookup] at run
  dsimp only at run
  by_cases zero : s.clock = 0
  · simp [zero] at run
  · rw [if_neg zero] at run
    have body := evaluate_sszCheckOffsets_body (callEntryStateHOLFinite s (reqCheckLocals offsets length))
      offsets 5 20 length code e1 e2 e3 e4 (by decide)
    have metadata := evaluateHOLFiniteState_metadata (callEntryStateHOLFinite s (reqCheckLocals offsets length))
      (sourceFunctionBody Guest.guestFn_ssz_check_offsets)
    have frame := evaluate_sszCheckOffsets_body_frame (callEntryStateHOLFinite s (reqCheckLocals offsets length)) code
    cases bodyRun : evaluateHOLFiniteState (callEntryStateHOLFinite s (reqCheckLocals offsets length))
        (sourceFunctionBody Guest.guestFn_ssz_check_offsets) with
    | mk result middle =>
      rw [bodyRun] at run body metadata frame
      dsimp only at body metadata frame
      cases result with
      | none => simp at run
      | some result =>
        cases result <;> simp only at run
        case returned value =>
          split at run
          · obtain ⟨_, ret⟩ := Prod.mk.inj run
            subst ret
            have contract := body.2.2.2.2 value rfl
            obtain ⟨m, g⟩ := frame (Or.inr (Or.inr (Or.inr ⟨value, rfl⟩)))
            have hv := contract.1
            subst hv
            exact ⟨contract, rfl, m, g, metadata.2.1, metadata.1⟩
          · simp at run
        all_goals simp at run

#print axioms reqCheck_bounded
#print axioms reqCheck_normal
end InitECandidate.Runtime
