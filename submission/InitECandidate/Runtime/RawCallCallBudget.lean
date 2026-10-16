import InitECandidate.Runtime.RawCallReturnBudget
namespace InitECandidate.Runtime.StackRawCall
open Flapjack Flapjack.Compiler.Backend Flapjack.Compiler.Backend.StackLang
open Flapjack.Compiler.Backend.StackRawCall
abbrev CallIH {width : Nat} [NeZero width] (C F : Type)
    (ret : Option (HolProg width × Nat × Nat × Nat)) (dest : Sum Nat Nat)
    (handler : Option (HolProg width × Nat × Nat))
    (source : StackSemStateFiniteExact width C F) : Prop :=
  match ret with
  | none => TailCalleeIH C F dest handler source
  | some (body, link, l1, l2) =>
      ReturnCalleeIH C F dest link l1 l2 source ∧
      ReturnContinuationIH C F body dest link l1 l2 source ∧
      ExceptionContinuationIH C F handler dest link l1 l2 source

theorem compCorrectCall {width : Nat} [NeZero width] {C F : Type}
    (ret : Option (HolProg width × Nat × Nat × Nat)) (dest : Sum Nat Nat)
    (handler : Option (HolProg width × Nat × Nat)) (info : Spt Nat)
    (source target post : StackSemStateFiniteExact width C F)
    (result : Option (StackSemResult width))
    (induction : CallIH C F ret dest handler source)
    (hypothesis : StackSemEvaluate.evaluate (.call ret dest handler, source) =
      (result, post) ∧ result ≠ some .error ∧ stateRel info source target) :
    BoundedSimulationResult (compTop info (.call ret dest handler)) info target post result (source.clock - post.clock - 1) ∧
    BoundedSimulationResult (comp info (.call ret dest handler)) info target post result (source.clock - post.clock - 1) := by
  cases ret with
  | none => exact compCorrectCallTail dest handler info source target post result induction hypothesis
  | some triple =>
      obtain ⟨body, link, l1, l2⟩ := triple
      obtain ⟨calleeIH, returnIH, exceptionIH⟩ := induction
      exact compCorrectCallReturn body link l1 l2 dest handler info source target post result
        calleeIH returnIH exceptionIH hypothesis


#print axioms compCorrectCall
end InitECandidate.Runtime.StackRawCall
