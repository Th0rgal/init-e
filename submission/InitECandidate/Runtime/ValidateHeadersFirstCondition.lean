import InitECandidate.Runtime.ValidateHeadersFirstSource
import InitECandidate.Runtime.VariableCountedLoop
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- The original signed comparison agrees with the natural loop rank under
the actual 256-header cap. -/
theorem eval_validate_headers_first_condition {F : Type} (s : PanSemStateFiniteExact 64 F)
    (index count : BitVec 64) (cap : count.toNat ≤ 256) (within : index.toNat ≤ count.toNat)
    (atIndex : s.locals.lookup (ofString "i") = some (.val (.word index)))
    (atCount : s.locals.lookup (ofString "n") = some (.val (.word count))) :
    evalHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a)) validateHeadersFirstCondition =
      some (.val (.word (if index.toNat < count.toNat then 1 else 0))) :=
  eval_variable_counted_condition s _ _ .less (Or.inl rfl) count index (by intro _; omega) within atIndex atCount

theorem validate_headers_first_condition_rank_zero {F : Type} (s : PanSemStateFiniteExact 64 F)
    (index count w : BitVec 64) (cap : count.toNat ≤ 256) (within : index.toNat ≤ count.toNat)
    (atIndex : s.locals.lookup (ofString "i") = some (.val (.word index)))
    (atCount : s.locals.lookup (ofString "n") = some (.val (.word count)))
    (rankZero : count.toNat - index.toNat = 0)
    (condition : evalHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a)) validateHeadersFirstCondition = some (.val (.word w))) :
    w = 0 := by
  rw [eval_validate_headers_first_condition s index count cap within atIndex atCount,
    if_neg (by omega)] at condition
  simpa using condition.symm

theorem validate_headers_first_condition_enabled {F : Type} (s : PanSemStateFiniteExact 64 F)
    (index count w : BitVec 64) (cap : count.toNat ≤ 256) (within : index.toNat ≤ count.toNat)
    (atIndex : s.locals.lookup (ofString "i") = some (.val (.word index)))
    (atCount : s.locals.lookup (ofString "n") = some (.val (.word count)))
    (condition : evalHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a)) validateHeadersFirstCondition = some (.val (.word w)))
    (nonzero : w ≠ 0) : index.toNat < count.toNat := by
  rw [eval_validate_headers_first_condition s index count cap within atIndex atCount] at condition
  by_contra outside
  rw [if_neg outside] at condition
  have zero : w = 0 := by simpa using condition.symm
  exact nonzero zero

#print axioms eval_validate_headers_first_condition
#print axioms validate_headers_first_condition_rank_zero
#print axioms validate_headers_first_condition_enabled
end InitECandidate.Runtime
