import InitECandidate.Runtime.ValidateHeadersSecondSource
import InitECandidate.Runtime.MemeqConstCallBound
import InitECandidate.Runtime.NormalLocalIncrementCalls
import InitECandidate.Runtime.NormalLocalFrame
import InitECandidate.Runtime.NoLoopControl
import InitECandidate.Runtime.PanEvaluationMetadata
import InitECandidate.Runtime.VariableCountedLoop
import InitECandidate.Runtime.HtabInsertRawFrame
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
set_option maxRecDepth 40000
set_option maxHeartbeats 3000000

/-- One iteration of the real second loop costs at most `4 * 32 + 1 = 129`
source ticks: the literal-32 `memeq` declaration call, plus a zero-tick
straight-line tail (`ok` guard and `i := i + 1`).  This holds for ANY argument
values and every outcome, in particular for failed loads or unusable windows,
which simply make the callee return an error. -/
def validateHeadersSecondIterationCost : Nat := 4 * 32 + 1

/-- The body of the real second loop, bounded in every outcome without any
readability assumption on the compared windows. -/
theorem progBounded_validate_headers_second_body :
    ProgBounded validateHeadersSecondBody validateHeadersSecondIterationCost :=
  memeq_decCall_const_progBounded (ofString "eq") validateHeadersSecondLeftArgument
    validateHeadersSecondRightArgument (32 : BitVec 64) (by decide)
    (ProgBounded.straight validateHeadersSecondContinuation (by decide))

/-- On a normal (non-raising) outcome the body always advances the loop index
by one, whatever the callee did and whatever the compared bytes were. -/
theorem validateHeadersSecondBody_increments :
    NormalLocalIncrement (ofString "i") validateHeadersSecondBody := by
  rw [source_validate_headers_second_body_split]
  apply normalLocalIncrement_decCall (ofString "i") (ofString "eq") (ofString "memeq") .one
    validateHeadersSecondArguments validateHeadersSecondContinuation (by decide)
  rw [validateHeadersSecondContinuation]
  exact normalLocalIncrement_guard (ofString "i") (ofString "BlockErr") _ _ _
    (normalLocalIncrement_assign (ofString "i"))

/-- A normal outcome of the body keeps the source bound local `n` untouched. -/
theorem validateHeadersSecondBody_keepsBound :
    normalLocalFrameSyntax (ofString "n") validateHeadersSecondBody = true := rfl

/-- The body never emits `break` or `continue`, including through the opaque
`memeq` callee. -/
theorem validateHeadersSecondBody_noLoopControl :
    noLoopControl validateHeadersSecondBody = true := rfl

/-- Loop invariant of the real second loop: the two integers it actually
compares are still the source locals `i`, `n`, the loop is still under the
source cap `n <= 256`, and the remaining-iteration rank is `n - i`.  Nothing
about memory or hashes is needed to bound the runtime. -/
def ValidateHeadersSecondCount (n : BitVec 64) {F : Type}
    (s : PanSemStateFiniteExact 64 F) (rank : Nat) : Prop :=
  ∃ i : BitVec 64,
    s.locals.lookup (ofString "i") = some (.val (.word i)) ∧
    s.locals.lookup (ofString "n") = some (.val (.word n)) ∧
    i.toNat ≤ n.toNat ∧ n.toNat ≤ 256 ∧ rank = n.toNat - i.toNat

/-- The real loop condition reads zero once the index has reached the bound,
so a nonzero condition always means `i < n`. -/
theorem validateHeadersSecondCondition_stopped {F : Type} (s : PanSemStateFiniteExact 64 F)
    (n i : BitVec 64)
    (atI : s.locals.lookup (ofString "i") = some (.val (.word i)))
    (atN : s.locals.lookup (ofString "n") = some (.val (.word n)))
    (within : i.toNat ≤ n.toNat) (small : n.toNat < 2 ^ 63) (stopped : ¬ i.toNat < n.toNat) :
    evalHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a)) validateHeadersSecondCondition =
      some (.val (.word 0)) := by
  have evaluated := eval_variable_counted_condition s (ofString "i") (ofString "n") .less (Or.inl rfl) n i
    (by omega) within atI atN
  simp only [validateHeadersSecondCondition]
  rw [evaluated]
  simp [stopped]

/-- The real second loop runs in at most `rank * 130` ticks in every outcome:
a normal exit has `i = n`, and any mismatch or failed call ends through the
source `raise BlockErr 2` inside the same per-iteration budget. -/
theorem validate_headers_second_loop_ranked (n : BitVec 64) :
    ∀ rank : Nat, ∀ {F : Type} (s : PanSemStateFiniteExact 64 F), s.code = originalRuntimeCode →
      ValidateHeadersSecondCount n s rank → rank * (validateHeadersSecondIterationCost + 1) ≤ s.clock →
      RankedOutcome s validateHeadersSecondCondition (rank * (validateHeadersSecondIterationCost + 1))
        (ValidateHeadersSecondCount n) False (evaluateHOLFiniteState s validateHeadersSecondLoop) := by
  have exit : ∀ {F : Type} (s : PanSemStateFiniteExact 64 F), ValidateHeadersSecondCount n s 0 →
      ∀ w : BitVec 64,
        evalHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a)) validateHeadersSecondCondition =
          some (.val (.word w)) → w = 0 := by
    intro F s ranked w evaluated
    obtain ⟨i, atI, atN, within, cap, ranking⟩ := ranked
    have condition := eval_variable_counted_condition s (ofString "i") (ofString "n") .less (Or.inl rfl)
      n i (by omega) within atI atN
    simp only [validateHeadersSecondCondition] at evaluated
    rw [condition] at evaluated
    have stopped : ¬ i.toNat < n.toNat := by omega
    simpa [stopped] using evaluated.symm
  apply rankedWhile_run validateHeadersSecondCondition validateHeadersSecondBody
    validateHeadersSecondIterationCost (ValidateHeadersSecondCount n) False exit
  intro F s rank w code ranked condition nonzero budget
  obtain ⟨i, atI, atN, within, cap, ranking⟩ := ranked
  have active : i.toNat < n.toNat := by
    by_contra inactive
    have stopped := validateHeadersSecondCondition_stopped s n i atI atN within (by omega) inactive
    have pair : some (ValueHOL.val (HolWordLab.word (0 : BitVec 64))) =
        some (ValueHOL.val (HolWordLab.word w)) := stopped.symm.trans condition
    have words : (0 : BitVec 64) = w := by
      have := Option.some.inj pair
      simpa using this
    exact nonzero words.symm
  have entered : (decClockHOLFinite s).code = originalRuntimeCode := code
  have ticks : validateHeadersSecondIterationCost ≤ (decClockHOLFinite s).clock := by
    have expanded : 4 * 32 + 1 + 1 ≤ s.clock := budget
    have clockStep : (decClockHOLFinite s).clock = s.clock - 1 := rfl
    rw [clockStep]
    change 4 * 32 + 1 ≤ s.clock - 1
    omega
  have bounded := progBounded_validate_headers_second_body (decClockHOLFinite s) entered ticks
  have controls := evaluate_noLoopControl validateHeadersSecondBody
    validateHeadersSecondBody_noLoopControl (decClockHOLFinite s)
  have metadata := evaluateHOLFiniteState_metadata (decClockHOLFinite s) validateHeadersSecondBody
  refine ⟨?_,?_,bounded.2.2,?_,?_⟩
  · change s.clock - 1 ≤ _ + validateHeadersSecondIterationCost
    exact bounded.1
  · change _ ≤ s.clock - 1
    exact bounded.2.1
  · intro normal
    have normal' : (evaluateHOLFiniteState (decClockHOLFinite s) validateHeadersSecondBody).1 = none := by
      rcases normal with quiet | continued
      · exact quiet
      · exact False.elim (controls.2 continued)
    let post := (evaluateHOLFiniteState (decClockHOLFinite s) validateHeadersSecondBody).2
    have run : evaluateHOLFiniteState (decClockHOLFinite s) validateHeadersSecondBody = (none,post) :=
      Prod.ext normal' rfl
    have dAtI : (decClockHOLFinite s).locals.lookup (ofString "i") = some (.val (.word i)) := atI
    have dAtN : (decClockHOLFinite s).locals.lookup (ofString "n") = some (.val (.word n)) := atN
    have advanced := validateHeadersSecondBody_increments (decClockHOLFinite s) post i dAtI run
    have keptBound := evaluate_normalLocalFrame (ofString "n") validateHeadersSecondBody
      validateHeadersSecondBody_keepsBound (decClockHOLFinite s) post run
    have keptN : post.locals.lookup (ofString "n") = some (.val (.word n)) := by
      rw [keptBound,dAtN]
    have natural : (i + (1 : BitVec 64)).toNat = i.toNat + 1 := word_add_toNat i 1 (by omega)
    have nextWithin : (i + (1 : BitVec 64)).toNat ≤ n.toNat := by rw [natural]; omega
    have nextRank : n.toNat - (i + (1 : BitVec 64)).toNat ≤ rank := by rw [natural]; omega
    have codeOk : post.code = s.code := by
      rw [metadata.1]
      rfl
    exact ⟨n.toNat - (i + (1 : BitVec 64)).toNat,nextRank,
      ⟨i + (1 : BitVec 64),advanced,keptN,nextWithin,cap,rfl⟩,codeOk⟩
  · intro broke
    exact (controls.1 broke).elim

/-- Every outcome of the real second loop from a live invariant stays inside
`rank * 130` source ticks. -/
theorem runBounded_validate_headers_second_loop {F : Type} (s : PanSemStateFiniteExact 64 F)
    (n : BitVec 64) (rank : Nat) (code : s.code = originalRuntimeCode)
    (ranked : ValidateHeadersSecondCount n s rank)
    (budget : rank * (validateHeadersSecondIterationCost + 1) ≤ s.clock) :
    RunBounded s validateHeadersSecondLoop (rank * (validateHeadersSecondIterationCost + 1)) := by
  obtain ⟨spent,kept,safe,_⟩ := validate_headers_second_loop_ranked n rank s code ranked budget
  exact ⟨spent,kept,safe⟩

/-- Under the source cap `n <= 256` every outcome of the real second loop fits
in the uniform `256 * 130 = 33280`-tick budget, for every entry index `i <= n`. -/
theorem runBounded_validate_headers_second_loop_cap {F : Type} (s : PanSemStateFiniteExact 64 F)
    (n : BitVec 64) (rank : Nat) (code : s.code = originalRuntimeCode)
    (ranked : ValidateHeadersSecondCount n s rank) (budget : 256 * 130 ≤ s.clock) :
    RunBounded s validateHeadersSecondLoop (256 * 130) := by
  have small : rank * (validateHeadersSecondIterationCost + 1) ≤ 256 * 130 := by
    obtain ⟨i, _, _, _, cap, ranking⟩ := ranked
    unfold validateHeadersSecondIterationCost
    omega
  exact (runBounded_validate_headers_second_loop s n rank code ranked (by omega)).weaken small

#print axioms progBounded_validate_headers_second_body
#print axioms validateHeadersSecondBody_increments
#print axioms validate_headers_second_loop_ranked
#print axioms runBounded_validate_headers_second_loop
#print axioms runBounded_validate_headers_second_loop_cap
end InitECandidate.Runtime
