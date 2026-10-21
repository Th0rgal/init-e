import InitECandidate.Runtime.SourceCostLoopLiveCallShortG
import InitECandidate.Runtime.SourceCostLoopLiveSequenceG
import InitECandidate.Runtime.SourceCostLoopLiveBranchG
import InitECandidate.Runtime.SourceCostLoopLiveLoopG
namespace InitECandidate.Runtime.FineCost
open Flapjack Flapjack.LoopSemStateFiniteExact

variable {L : LeafPrice}

private theorem cut_nonerrorG {F : Type} {live : NumSet}
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
theorem LoopWorkG.live_paid {F : Type} {s : LoopSemStateFiniteExact 64 F} {p : HolLoopProg 64}
    {output : Option (LoopResultExact 64) × LoopSemStateFiniteExact 64 F} {w : Nat}
    (work : LoopWorkG L s p output w) (nonerror : output.1 ≠ some .error) :
    LoopLivePaidG L s p output w := by
  induction work with
  | @atom s p output cost leaf run =>
    exact loop_live_paid_leafG (LoopWorkG.atom leaf run) leaf nonerror
  | mark inner ih => exact loop_live_paid_markG (ih nonerror)
  | seqNext one two ihOne ihTwo =>
    exact loop_live_paid_seq_nextG (ihOne (by simp)) (ihTwo nonerror)
  | seqStop one ih => exact loop_live_paid_seq_stopG (ih nonerror)
  | iteBranch lhs rhs branch ih =>
    exact loop_live_paid_iteG lhs rhs branch (ih (cut_nonerrorG nonerror)) nonerror
  | iteInvalid invalid => exact False.elim (nonerror rfl)
  | @loopNext s liveIn body liveOut entry result middle output wb wr cut one again rest ihOne ihRest =>
    have bodyOk : result ≠ some .error := by rcases again with rfl | rfl <;> simp
    exact loop_live_paid_loop_nextG cut again (ihOne bodyOk) (ihRest nonerror)
  | loopBreak cut one ih => exact loop_live_paid_loop_breakG cut one (ih (by simp)) nonerror
  | @loopExit s liveIn body liveOut entry result middle wb cut one stop ih =>
    have bodyOk : result ≠ some .error := by
      rintro rfl
      exact nonerror rfl
    exact loop_live_paid_loop_exitG cut one stop (ih bodyOk) nonerror
  | loopCut stopped => exact loop_live_paid_loop_cutG stopped nonerror
  | @callShort s returns target arguments handler output short run =>
    exact loop_live_paid_call_shortG short run nonerror
  | callTail args find noHandler clock body ih =>
    exact loop_live_paid_call_tailG args find noHandler clock body nonerror
  | @callRet s names live target arguments handler values env prog entry result post wb
      args find nodup cut body plain ih =>
    cases handler with
    | none => exact loop_live_paid_call_ret_plainG args find nodup cut body nonerror
    | some pair =>
      rcases pair with ⟨exceptionName, handlerProgram, continuation, liveOut⟩
      exact loop_live_paid_call_ret_handlerG args find nodup cut body plain nonerror
  | callRetCont args find nodup cut body lengths cont ihBody ihCont =>
    exact loop_live_paid_call_contG args find nodup cut body lengths cont
      (ihCont (cut_nonerrorG nonerror)) nonerror
  | callHandle args find nodup cut body handle ihBody ihHandle =>
    exact loop_live_paid_call_handleG args find nodup cut body handle
      (ihHandle (cut_nonerrorG nonerror)) nonerror

#print axioms LoopWorkG.live_paid
end InitECandidate.Runtime.FineCost
