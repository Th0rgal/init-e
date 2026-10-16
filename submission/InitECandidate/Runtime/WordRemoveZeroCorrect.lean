import InitECandidate.Runtime.WordRemoveZeroReturning
import InitECandidate.Runtime.WordRemoveZeroLeaves
namespace InitECandidate.Runtime.WordRemove
open Flapjack Flapjack.WordSemStateFiniteExact
open Flapjack.Compiler.Backend.WordRemove

/-- Full zero-extra-fuel removal theorem for all Word constructors. The source
zero-term-depth premise is part of ZeroRemoveProp, not an induction assumption. -/
theorem zeroRemove_correct {width : Nat} [NeZero width] {C F : Type}
    (c : WordCompileFn width C) (p : WordLangProgHOL (BitVec width))
    (s : WordSemStateFiniteExact width C F) : ZeroRemoveProp c p s := by
  cases p
  case seq a b =>
    apply zeroRemove_seq
    · exact zeroRemove_correct c a s
    · intro middle run
      have lower := (evaluate_clock a s none middle run).1
      exact zeroRemove_correct c b middle
  case ite cmp reg ri a b =>
    exact zeroRemove_if c cmp reg ri a b s (zeroRemove_correct c a s) (zeroRemove_correct c b s)
  case loop names body exits =>
    apply zeroRemove_loop
    · intro cutSource cut
      have same := (cutState_clock_termdep _ _ _ cut).1
      exact zeroRemove_correct c body cutSource
    · intro cutSource cut result middle run continuing positive
      have same := (cutState_clock_termdep _ _ _ cut).1
      have lower := (evaluate_clock body cutSource result middle run).1
      exact zeroRemove_correct c (.loop names body exits) (decClock middle)
  case call ret dest args handler =>
    rcases ret with _ | ⟨values,names,retCode,l1,l2⟩
    · apply zeroRemove_tail
      intro actualArgs body ss positive
      exact zeroRemove_correct c body (WordSemStateFiniteExact.callEnv actualArgs ss (decClock s))
    · apply zeroRemove_return
      intro child next smaller
      exact zeroRemove_correct c child next
  case mustTerminate body => exact zeroRemove_mustTerminate c body s
  case tick => exact zeroRemove_tick c s
  case install ptr len dptr dlen names => exact zeroRemove_install c s ptr len dptr dlen names
  all_goals exact zeroRemove_leaf c _ s rfl (by intros; nofun) rfl
termination_by (s.clock,sizeOf p)
decreasing_by
  all_goals simp_wf
  all_goals simp_all [Prod.lex_def, WordSemStateFiniteExact.callEnv, decClock]
  all_goals omega

#print axioms zeroRemove_correct
end InitECandidate.Runtime.WordRemove
