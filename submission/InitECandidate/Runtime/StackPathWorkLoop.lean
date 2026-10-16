import InitECandidate.Runtime.StackPathWorkControl
namespace InitECandidate.Runtime.StackToLab
open Flapjack Flapjack.Compiler.Backend.StackLang
open Flapjack.Compiler.Encoders.Asm
open Flapjack.StackSemStateOps Flapjack.StackSemControl
theorem pathWork_loop_bound {width : Nat} [NeZero width] {C F : Type}
    (body : HolProg width) (s : StackSemStateFiniteExact width C F)
    (first : BoundedFlattenProp body s (pathWork body s))
    (next : ∀ (result : Option (StackSemResult width)) (middle : StackSemStateFiniteExact width C F),
      StackSemEvaluate.evaluate (body, s) = (result, middle) →
      contLoop result = true → middle.clock ≠ 0 →
      BoundedFlattenProp (.loop body) (decClock middle) (pathWork (.loop body) (decClock middle))) :
    BoundedFlattenProp (.loop body) s (pathWork (.loop body) s) := by
  let returned := StackSemEvaluate.evaluate (body, s)
  let rest := if contLoop returned.1 && returned.2.clock != 0 then
      pathWork (.loop body) (decClock returned.2) else 0
  have following : ∀ (result : Option (StackSemResult width)) (middle : StackSemStateFiniteExact width C F),
      StackSemEvaluate.evaluate (body, s) = (result, middle) →
      contLoop result = true → middle.clock ≠ 0 →
      BoundedFlattenProp (.loop body) (decClock middle) rest := by
    intro result middle run continuing positive
    have restEq : rest = pathWork (.loop body) (decClock middle) := by
      simp [rest, returned, run, continuing, positive]
    rw [restEq]
    exact next result middle run continuing positive
  have composed := flattenLoop_reached_bounded s body (pathWork body s) rest first following
  intro t r final n l cs bs target hyps
  apply boundedFlattenConcl_mono (a := pathWork body s + rest) _
    (composed t r final n l cs bs target hyps)
  rw [pathWork, StackSemEvaluateClock.fixClockEvaluate]
  change pathWork body s + rest ≤ 2 + pathWork body s + rest
  omega


#print axioms pathWork_loop_bound
end InitECandidate.Runtime.StackToLab
