import InitECandidate.Runtime.AuthorizationsStepProgress
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- Consecutive actual normal iteration evaluations, each entered inside the
fixed outer-list count. This records successful steps, including their states. -/
inductive SuccessfulAuthorizationSteps {F : Type} (count : BitVec 64) :
    PanSemStateFiniteExact 64 F → PanSemStateFiniteExact 64 F → Nat → Prop
  | done (state) : SuccessfulAuthorizationSteps count state state 0
  | step (state middle post : PanSemStateFiniteExact 64 F) (index : BitVec 64) (steps : Nat)
      (binding : state.locals.lookup (ofString "i") = some (.val (.word index)))
      (inside : index.toNat < count.toNat)
      (run : evaluateHOLFiniteState state authorizationStep = (none,middle))
      (rest : SuccessfulAuthorizationSteps count middle post steps) :
      SuccessfulAuthorizationSteps count state post (steps + 1)

/-- Successful execution consumes exactly one unit of the remaining-entry rank. -/
theorem authorization_step_rank_exact {F : Type} (state post : PanSemStateFiniteExact 64 F)
    (index count : BitVec 64)
    (binding : state.locals.lookup (ofString "i") = some (.val (.word index)))
    (inside : index.toNat < count.toNat)
    (run : evaluateHOLFiniteState state authorizationStep = (none,post)) :
    authorizationRank count post + 1 = authorizationRank count state := by
  obtain ⟨advanced,nextNat,_⟩ := evaluate_authorization_step_rank_progress state post index count binding inside run
  simp only [authorizationRank,binding,advanced]
  rw [nextNat]
  omega

/-- Every concrete successful trace has length bounded by its initial rank;
the equality also identifies exactly the unprocessed suffix. -/
theorem SuccessfulAuthorizationSteps.rank_accounting {F : Type} {count : BitVec 64}
    {state post : PanSemStateFiniteExact 64 F} {steps : Nat}
    (trace : SuccessfulAuthorizationSteps count state post steps) :
    steps + authorizationRank count post = authorizationRank count state := by
  induction trace with
  | done state => simp
  | step state middle post index steps binding inside run rest ih =>
    have one := authorization_step_rank_exact state middle index count binding inside run
    omega

theorem SuccessfulAuthorizationSteps.length_le_count {F : Type} {count : BitVec 64}
    {state post : PanSemStateFiniteExact 64 F} {steps : Nat}
    (trace : SuccessfulAuthorizationSteps count state post steps) : steps ≤ count.toNat := by
  have accounting := trace.rank_accounting
  have initial : authorizationRank count state ≤ count.toNat := by
    unfold authorizationRank
    split <;> omega
  omega

#print axioms authorization_step_rank_exact
#print axioms SuccessfulAuthorizationSteps.rank_accounting
#print axioms SuccessfulAuthorizationSteps.length_le_count
end InitECandidate.Runtime
