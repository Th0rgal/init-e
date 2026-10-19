import InitECandidate.Runtime.DecodeWitnessRootComparisonBounded
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

def decodeWitnessEmptyGuard : ProgHOL 64 :=
  .ite (.cmp .notEqual (.var .local (ofString "is_empty")) (.const 0)) (.return (.const 0)) .skip

theorem source_decode_witness_empty_guard : decodeWitnessAt 1 =
    .seq decodeWitnessEmptyGuard (decodeWitnessAt 2) := by
  unfold decodeWitnessAt decodeWitnessEmptyGuard sourceFunctionBody
  rw [InitECandidate.Proofs.FrontendCodecComputation.declToHOL_eq]
  rfl

/-- The original guard either continues with the exact same state or returns
its empty-root result immediately. Both branches spend zero source steps. -/
theorem evaluate_decode_witness_empty_guard {F : Type} (s : PanSemStateFiniteExact 64 F) (word : BitVec 64)
    (atWord : s.locals.lookup (ofString "is_empty") = some (.val (.word word))) :
    evaluateHOLFiniteState s (decodeWitnessAt 1) =
      if word = 0 then evaluateHOLFiniteState s (decodeWitnessAt 2)
      else (some (.returned (.val (.word (0#64)))),emptyLocalsHOLFinite s) := by
  rw [source_decode_witness_empty_guard,evaluateHOLFiniteState_seq_line780]
  have first : evaluateHOLFiniteState s decodeWitnessEmptyGuard =
      if word = 0 then (none,s) else (some (.returned (.val (.word (0#64)))),emptyLocalsHOLFinite s) := by
    simp [decodeWitnessEmptyGuard,evaluateHOLFiniteState_ite,evalHOLExact,atWord,
      Compiler.Encoders.Asm.wordCmpHOL,evaluateHOLFiniteState_return,evaluateHOLFiniteState_skip,shapeOfHOLExact]
  rw [first]
  split <;> rfl

/-- Only a zero comparison result reaches the lookup; the nonzero case already
returned successfully and does not require a lookup or node-decoder bound. -/
theorem runBounded_decode_witness_empty_guard {F : Type} (s : PanSemStateFiniteExact 64 F)
    (word : BitVec 64) (cost : Nat)
    (atWord : s.locals.lookup (ofString "is_empty") = some (.val (.word word)))
    (continuation : word = 0 → RunBounded s (decodeWitnessAt 2) cost) :
    RunBounded s (decodeWitnessAt 1) cost := by
  unfold RunBounded
  rw [evaluate_decode_witness_empty_guard s word atWord]
  split
  · rename_i zero
    exact continuation zero
  · simp [emptyLocalsHOLFinite]

/-- The lookup entry on the continuing branch is precisely the guard entry. -/
theorem decode_witness_empty_guard_zero_reaches {F : Type} (s : PanSemStateFiniteExact 64 F)
    (atWord : s.locals.lookup (ofString "is_empty") = some (.val (.word (0#64)))) :
    Reaches s (decodeWitnessAt 1) (fun post => post = s) 0 (decodeWitnessAt 2) := by
  refine Or.inl ⟨s,rfl,by omega,le_refl _,?_⟩
  rw [evaluate_decode_witness_empty_guard s 0 atWord,if_pos rfl]
  exact scoped_refl _

#print axioms evaluate_decode_witness_empty_guard
#print axioms runBounded_decode_witness_empty_guard
#print axioms decode_witness_empty_guard_zero_reaches
end InitECandidate.Runtime
