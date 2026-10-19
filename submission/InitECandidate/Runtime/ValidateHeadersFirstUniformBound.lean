import InitECandidate.Runtime.ValidateHeadersFirstLoopBound
import InitECandidate.Runtime.HeaderDecoderCostPolynomial
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact

/-- Uniform source-step budget for the original capped first loop. -/
def validateHeadersFirstLoopCost (inputLimit : Nat) : Nat :=
  256 * (validateHeadersFirstIterationCost inputLimit + 1)

theorem validate_headers_first_invariant_rank_bound {F : Type} (e : ValidateHeadersFirstEnvironment)
    (s : PanSemStateFiniteExact 64 F) (rank : Nat) (valid : ValidateHeadersFirstInvariant e s rank) :
    rank ≤ 256 := by
  obtain ⟨index,heap,arr,n,i,hs,hashes,within,distance,rest⟩ := valid
  have cap := e.cap
  omega

/-- Every outcome of the actual first while loop consumes at most the
uniform capped budget; this includes failing decoder, store and hash paths. -/
theorem runBounded_validate_headers_first_loop {F : Type} (e : ValidateHeadersFirstEnvironment)
    (s : PanSemStateFiniteExact 64 F) (rank : Nat) (code : s.code = originalRuntimeCode)
    (valid : ValidateHeadersFirstInvariant e s rank)
    (budget : validateHeadersFirstLoopCost e.inputLimit ≤ s.clock) :
    RunBounded s (.while validateHeadersFirstCondition validateHeadersFirstBody) (validateHeadersFirstLoopCost e.inputLimit) := by
  have rankBound := validate_headers_first_invariant_rank_bound e s rank valid
  have smaller : rank * (validateHeadersFirstIterationCost e.inputLimit + 1) ≤ validateHeadersFirstLoopCost e.inputLimit :=
    Nat.mul_le_mul_right _ rankBound
  have result := validate_headers_first_loop_ranked e rank s code valid (by omega)
  exact ⟨by have spent := result.1; omega,result.2.1,result.2.2.1⟩

/-- Explicit quadratic source budget, with the input size still symbolic. -/
theorem validateHeadersFirstLoopCost_polynomial (limit : Nat) :
    validateHeadersFirstLoopCost limit = 222720 * limit * limit + 260608 * limit + 664269824 := by
  simp only [validateHeadersFirstLoopCost,validateHeadersFirstIterationCost,headerDecoderBodyCost_polynomial]
  ring

#print axioms validate_headers_first_invariant_rank_bound
#print axioms runBounded_validate_headers_first_loop
#print axioms validateHeadersFirstLoopCost_polynomial
end InitECandidate.Runtime
