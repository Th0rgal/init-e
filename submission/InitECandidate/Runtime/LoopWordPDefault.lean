import InitECandidate.Runtime.LoopWordP
namespace InitECandidate.Runtime.FineCost
open Flapjack Flapjack.WordSemStateFiniteExact

/-! The fixed prices are an instance: `LoopWork` is `LoopWorkP defaultLoopPrice`
and `loopWordPrice` is dominated by it, so `loop_to_word_cost` is a corollary of
`loop_to_word_costP`. -/

theorem LoopWork.toP {F : Type} {s : LoopSemStateFiniteExact 64 F} {p : HolLoopProg 64} {output w}
    (work : LoopWork s p output w) : LoopWorkP defaultLoopPrice s p output w := by
  induction work with
  | atom leaf run => exact .atom leaf run
  | mark inner ih => exact .mark ih
  | seqNext one two ih1 ih2 => exact .seqNext ih1 ih2
  | seqStop one ih => exact .seqStop ih
  | iteBranch lhs rhs branch ih => exact .iteBranch lhs rhs ih
  | iteInvalid invalid => exact .iteInvalid invalid
  | loopNext cut one again rest ih1 ih2 => exact .loopNext cut ih1 again ih2
  | loopBreak cut one ih => exact .loopBreak cut ih
  | loopExit cut one stop ih => exact .loopExit cut ih stop
  | loopCut stopped => exact .loopCut stopped
  | callShort short run => simpa [defaultLoopPrice] using LoopWorkP.callShort (lp := defaultLoopPrice) short run
  | callTail args find noHandler clock body ih =>
    simpa [defaultLoopPrice] using LoopWorkP.callTail args find noHandler clock ih
  | callRet args find nodup cut body plain ih =>
    simpa [defaultLoopPrice] using LoopWorkP.callRet args find nodup cut ih plain
  | @callRetCont s names live target arguments exceptionName handlerProgram continuation liveOut
      values env prog entry returned post wb output wc args find nodup cut body lengths cont ih1 ih2 =>
    have := LoopWorkP.callRetCont (exceptionName := exceptionName) (handlerProgram := handlerProgram)
      (liveOut := liveOut) args find nodup cut ih1 lengths ih2
    simp only [defaultLoopPrice, Nat.one_mul] at this
    exact this
  | @callHandle s names live target arguments exceptionName handlerProgram continuation liveOut
      values env prog entry exn post wb output wh args find nodup cut body handle ih1 ih2 =>
    have := LoopWorkP.callHandle (continuation := continuation) (liveOut := liveOut) args find nodup cut ih1 ih2
    simp only [defaultLoopPrice, Nat.one_mul] at this
    exact this

open Classical in
/-- `loopWordPrice` is dominated by the default Loop prices. -/
noncomputable def loopWordDominates {C F : Type} : WordDominates (C := C) (F := F) loopWordPrice defaultLoopPrice where
  T := 1
  I := 1
  L := 1
  U := 1
  argW := fun n => n
  R := 1
  seqZero := fun _ _ _ => by simp [loopWordPrice]
  skipZero := fun _ => by simp [loopWordPrice]
  tick := fun _ => by simp [loopWordPrice]
  ite := fun _ _ _ _ _ _ => by simp [loopWordPrice]
  loop := fun _ _ _ _ => by simp [loopWordPrice]
  leafOk := fun ctxt p l s cost leaf => loop_word_leaf ctxt p l cost leaf s
  tailCall := fun _ args _ _ => by simp [loopWordPrice]; omega
  retCall := fun _ _ _ _ _ _ _ _ _ => by rw [loopWordPrice]; simp
  iteOk := by decide
  iterOk := by decide
  tailOk := by decide
  argOk := fun n => by simp [defaultLoopPrice]; omega
  retOk := by decide
  contOk := by decide

/-- Loop-to-Word executed cost: from any Word state related to the Loop state
as in the pinned `compile_correct`, the compiled program's executed Word work
under `loopWordPrice` is at most the `LoopWork` of the same non-error run. -/
theorem loop_to_word_cost {C F : Type} {s : LoopSemStateFiniteExact 64 F} {p : HolLoopProg 64} {output w}
    (work : LoopWork s p output w) : WordCostLe C s p output w :=
  loop_to_word_costP (C := C) loopWordDominates work.toP

#print axioms LoopWork.toP
#print axioms loop_to_word_cost
end InitECandidate.Runtime.FineCost
