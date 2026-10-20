import InitECandidate.Runtime.SourceCostLoopLiveCallShort
import InitECandidate.Runtime.SourceCostLoopLiveSequence
import InitECandidate.Runtime.SourceCostLoopLiveBranch
import InitECandidate.Runtime.SourceCostLoopLiveLoop
namespace InitECandidate.Runtime.FineCost
open Flapjack Flapjack.LoopSemStateFiniteExact

private theorem cut_nonerror {F : Type} {live : NumSet}
    {output : Option (LoopResultExact 64) × LoopSemStateFiniteExact 64 F}
    (nonerror : (cutRes live output).1 ≠ some .error) : output.1 ≠ some .error := by
  rintro error
  rcases output with ⟨result, post⟩
  simp only at error
  subst error
  exact nonerror rfl

/-- Full actual liveness compiler transfer. Every non-error executed trace
supplies a trace of the real shrink output with no greater work, under exactly
the original input projection and result-indexed successor locals relation. -/
theorem LoopWork.live_paid {F : Type} {s : LoopSemStateFiniteExact 64 F} {p : HolLoopProg 64}
    {output : Option (LoopResultExact 64) × LoopSemStateFiniteExact 64 F} {w : Nat}
    (work : LoopWork s p output w) (nonerror : output.1 ≠ some .error) :
    LoopLivePaid s p output w := by
  induction work with
  | @atom s p output cost leaf run =>
    exact loop_live_paid_leaf (LoopWork.atom leaf run) leaf nonerror
  | mark inner ih => exact loop_live_paid_mark (ih nonerror)
  | seqNext one two ihOne ihTwo =>
    exact loop_live_paid_seq_next (ihOne (by simp)) (ihTwo nonerror)
  | seqStop one ih => exact loop_live_paid_seq_stop (ih nonerror)
  | iteBranch lhs rhs branch ih =>
    exact loop_live_paid_ite lhs rhs branch (ih (cut_nonerror nonerror)) nonerror
  | iteInvalid invalid => exact False.elim (nonerror rfl)
  | @loopNext s liveIn body liveOut entry result middle output wb wr cut one again rest ihOne ihRest =>
    have bodyOk : result ≠ some .error := by rcases again with rfl | rfl <;> simp
    exact loop_live_paid_loop_next cut again (ihOne bodyOk) (ihRest nonerror)
  | loopBreak cut one ih => exact loop_live_paid_loop_break cut one (ih (by simp)) nonerror
  | @loopExit s liveIn body liveOut entry result middle wb cut one stop ih =>
    have bodyOk : result ≠ some .error := by
      rintro rfl
      exact nonerror rfl
    exact loop_live_paid_loop_exit cut one stop (ih bodyOk) nonerror
  | loopCut stopped => exact loop_live_paid_loop_cut stopped nonerror
  | @callShort s returns target arguments handler output short run =>
    exact loop_live_paid_call_short short run nonerror
  | callTail args find noHandler clock body ih =>
    exact loop_live_paid_call_tail args find noHandler clock body nonerror
  | @callRet s names live target arguments handler values env prog entry result post wb
      args find nodup cut body plain ih =>
    cases handler with
    | none => exact loop_live_paid_call_ret_plain args find nodup cut body nonerror
    | some pair =>
      rcases pair with ⟨exceptionName, handlerProgram, continuation, liveOut⟩
      exact loop_live_paid_call_ret_handler args find nodup cut body plain nonerror
  | callRetCont args find nodup cut body lengths cont ihBody ihCont =>
    exact loop_live_paid_call_cont args find nodup cut body lengths cont
      (ihCont (cut_nonerror nonerror)) nonerror
  | callHandle args find nodup cut body handle ihBody ihHandle =>
    exact loop_live_paid_call_handle args find nodup cut body handle
      (ihHandle (cut_nonerror nonerror)) nonerror

#print axioms LoopWork.live_paid
end InitECandidate.Runtime.FineCost
