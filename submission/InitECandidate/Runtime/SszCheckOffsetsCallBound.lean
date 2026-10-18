import InitECandidate.Runtime.SszCheckOffsetsBody
import InitECandidate.Runtime.PanFourWordLookup
import InitECandidate.Runtime.CallBodyClockNoTimeout
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- The original offset checker, including its function-entry tick and every
rejection path, uses at most 2n+2 source clocks. -/
theorem evaluate_sszCheckOffsets_call_bounded {F : Type} (state : PanSemStateFiniteExact 64 F)
    (destination : Option (VarKind × MlS)) (arguments : List (ExpHOL 64))
    (offsets count fixed length : BitVec 64)
    (args : evalListHOLFinite state (h := fun address => Classical.propDecidable (state.memaddrs address)) arguments =
      some [.val (.word offsets),.val (.word count),.val (.word fixed),.val (.word length)])
    (code : state.code = originalRuntimeCode) (small : count.toNat < 2 ^ 63)
    (budget : 2 * count.toNat + 2 ≤ state.clock) :
    let evaluated := evaluateHOLFiniteState state (.call (some (destination,none)) (ofString "ssz_check_offsets") arguments)
    state.clock ≤ evaluated.2.clock + (2 * count.toNat + 2) ∧ evaluated.2.clock ≤ state.clock ∧
      evaluated.1 ≠ some .timeOut := by
  let callee : HolFiniteMapExact MlS (ValueHOL 64) :=
    (((HolFiniteMapExact.empty.update (ofString "offs",.val (.word offsets))).update
      (ofString "n",.val (.word count))).update (ofString "fixed",.val (.word fixed))).update
      (ofString "len",.val (.word length))
  let entry := callEntryStateHOLFinite state callee
  have atOffsets : entry.locals.lookup (ofString "offs") = some (.val (.word offsets)) := by
    simp [entry,callee,callEntryStateHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,
      show ofString "n" ≠ ofString "offs" by decide,show ofString "fixed" ≠ ofString "offs" by decide,
      show ofString "len" ≠ ofString "offs" by decide]
  have atCount : entry.locals.lookup (ofString "n") = some (.val (.word count)) := by
    simp [entry,callee,callEntryStateHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,
      show ofString "fixed" ≠ ofString "n" by decide,show ofString "len" ≠ ofString "n" by decide]
  have atFixed : entry.locals.lookup (ofString "fixed") = some (.val (.word fixed)) := by
    simp [entry,callee,callEntryStateHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,
      show ofString "len" ≠ ofString "fixed" by decide]
  have atLength : entry.locals.lookup (ofString "len") = some (.val (.word length)) := by
    simp [entry,callee,callEntryStateHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]
  have bounded := evaluate_sszCheckOffsets_body entry offsets count fixed length code
    atOffsets atCount atFixed atLength small
  have lookup := pan_four_word_lookup state.code.lookup (ofString "ssz_check_offsets")
    (ofString "offs") (ofString "n") (ofString "fixed") (ofString "len")
    (sourceFunctionBody Guest.guestFn_ssz_check_offsets) offsets count fixed length
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by rw [code]; exact originalRuntimeCode_sszCheckOffsets_lookup)
  cases bodyRun : evaluateHOLFiniteState entry (sourceFunctionBody Guest.guestFn_ssz_check_offsets) with
  | mk result post =>
    rw [bodyRun] at bounded
    dsimp only at bounded
    have output := evaluate_call_body_clock_no_timeout state post (ofString "ssz_check_offsets") destination arguments _
      (sourceFunctionBody Guest.guestFn_ssz_check_offsets) callee .one result args lookup (by omega) bodyRun
      (bounded.2.2.1 (by change 2 * count.toNat + 1 ≤ state.clock - 1; omega))
    dsimp only
    rw [output.2]
    refine ⟨?_,?_,output.1⟩
    · have spent := bounded.1
      change state.clock - 1 ≤ post.clock + (2 * count.toNat + 1) at spent
      change state.clock ≤ post.clock + (2 * count.toNat + 2)
      omega
    · have remaining := bounded.2.1
      change post.clock ≤ state.clock - 1 at remaining
      change post.clock ≤ state.clock
      omega

#print axioms evaluate_sszCheckOffsets_call_bounded
end InitECandidate.Runtime
