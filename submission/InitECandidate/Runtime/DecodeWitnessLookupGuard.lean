import InitECandidate.Runtime.DecodeWitnessLookupReach
import InitECandidate.Runtime.MptFailCallBound
import InitECandidate.Runtime.NoDirectReturn
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

def decodeWitnessLookupGuard : ProgHOL 64 :=
  .ite (.cmp .equal (.rfield 0 (.var .local (ofString "r"))) (.const 0))
    (.call (some (none,none)) (ofString "mpt_fail") [.const 1]) .skip

theorem source_decode_witness_lookup_guard : decodeWitnessAt 3 =
    .seq decodeWitnessLookupGuard (decodeWitnessAt 4) := by
  unfold decodeWitnessAt decodeWitnessLookupGuard sourceFunctionBody
  rw [InitECandidate.Proofs.FrontendCodecComputation.declToHOL_eq]
  rfl

/-- The actual missing-key guard terminates through mpt_fail or reaches node
decoding with a nonzero lookup flag. No normal missing-key path is assumed away. -/
theorem decode_witness_lookup_guard_reaches {F : Type} (s : PanSemStateFiniteExact 64 F)
    (found source length : BitVec 64)
    (atResult : s.locals.lookup (ofString "r") =
      some (.rStruct [.val (.word found),.val (.word source),.val (.word length)]))
    (code : s.code = originalRuntimeCode) (ticks : s.clock ≠ 0) :
    Reaches s (decodeWitnessAt 3) (fun next => found ≠ 0 ∧ next = s) 1 (decodeWitnessAt 4) := by
  rw [source_decode_witness_lookup_guard]
  have guardRun : evaluateHOLFiniteState s decodeWitnessLookupGuard =
      if found = 0 then evaluateHOLFiniteState s
        (.call (some (none,none)) (ofString "mpt_fail") [.const 1]) else (none,s) := by
    simp [decodeWitnessLookupGuard,evaluateHOLFiniteState_ite,evalHOLExact,atResult,
      Compiler.Encoders.Asm.wordCmpHOL]
  by_cases missing : found = 0
  · have fail := evaluate_mptFail_call_bounded s (.const 1) 1 code ticks
      (by rw [evalListHOLFinite_eq_toExact]; rfl)
    have noReturn := evaluate_noDirectReturn
      (.call (some (none,none)) (ofString "mpt_fail") [.const 1]) rfl s
    have abort : StAbort s (evaluateHOLFiniteState s decodeWitnessLookupGuard) 1 := by
      rw [guardRun,if_pos missing]
      cases run : evaluateHOLFiniteState s (.call (some (none,none)) (ofString "mpt_fail") [.const 1]) with
      | mk result post =>
        rw [run] at fail noReturn
        cases result with
        | none => exact False.elim (fail.2.2 rfl)
        | some result =>
          exact ⟨result,rfl,(by intro value equal; exact noReturn value (congrArg some equal)),
            by omega,by omega,fun _ => by simpa using fail.2.1⟩
    exact Or.inr (stAbort_seq s decodeWitnessLookupGuard (decodeWitnessAt 4) 1 abort)
  · refine Or.inl ⟨s,⟨missing,rfl⟩,by omega,le_refl _,?_⟩
    rw [evaluateHOLFiniteState_seq_line780,guardRun,if_neg missing]
    exact scoped_refl _

#print axioms source_decode_witness_lookup_guard
#print axioms decode_witness_lookup_guard_reaches
end InitECandidate.Runtime
