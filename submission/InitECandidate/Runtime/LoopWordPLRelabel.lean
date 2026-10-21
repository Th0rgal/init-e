import InitECandidate.Runtime.LoopWorkPL
namespace InitECandidate.Runtime.FineCost
open Flapjack Flapjack.LoopSemStateFiniteExact

/-! Labels enter at the final optimised Loop boundary. An unlabeled run at the
base prices becomes a labelled run whose extra work is exactly the labelled
surcharge trace: the same run's work under the surcharge-only price. Bounding
that trace (call-occurrence provenance) is a separate obligation. -/

/-- The surcharges of a labelled price alone: every base price is zero. -/
def surOnly (lp : LoopPriceL) : LoopPriceL where
  base :=
    { leaf := fun p => (lp.base.leaf p).map (fun _ => 0)
      ite := 0
      iter := 0
      call := 0
      argCost := fun _ => 0
      ret := 0
      cont := 0 }
  site := lp.site
  tail := lp.tail
  retNames := lp.retNames

/-- Relabelling: from an unlabeled run at `lp.base`, at any compiler label,
the labelled run costs at most its base work plus its surcharge trace. -/
theorem LoopWorkP.relabel {F : Type} {lp : LoopPriceL} {s : LoopSemStateFiniteExact 64 F} {p : HolLoopProg 64}
    {output} {w : Nat} (work : LoopWorkP lp.base s p output w) :
    ∀ l : Nat × Nat, ∃ S w', LoopWorkPL (surOnly lp) l s p output S ∧ LoopWorkPL lp l s p output w' ∧ w' ≤ w + S := by
  induction work with
  | atom leaf run =>
    intro l
    exact ⟨0, _, .atom (by simp [surOnly, leaf]) run, .atom leaf run, by omega⟩
  | mark _ ih =>
    intro l; obtain ⟨S, w', a, b, h⟩ := ih l; exact ⟨S, w', .mark a, .mark b, h⟩
  | @seqNext s first second middle output a b _ _ ih1 ih2 =>
    intro l
    obtain ⟨S1, w1, a1, b1, h1⟩ := ih1 l
    obtain ⟨S2, w2, a2, b2, h2⟩ := ih2 (labAfter first l)
    exact ⟨S1 + S2, w1 + w2, .seqNext a1 a2, .seqNext b1 b2, by omega⟩
  | seqStop _ ih =>
    intro l; obtain ⟨S, w', a, b, h⟩ := ih l; exact ⟨S, w', .seqStop a, .seqStop b, h⟩
  | @iteBranch s operator register right yes no live x y output w lhs rhs _ ih =>
    intro l
    obtain ⟨S, w', a, b, h⟩ := ih (if Compiler.Encoders.Asm.wordCmpHOL operator x y then l else labAfter yes l)
    exact ⟨0 + S, _, .iteBranch lhs rhs a, .iteBranch lhs rhs b, by first | omega | (simp only [surOnly]; omega)⟩
  | iteInvalid invalid =>
    intro l; exact ⟨1, 1, .iteInvalid invalid, .iteInvalid invalid, by omega⟩
  | loopNext cut _ again _ ih1 ih2 =>
    intro l
    obtain ⟨S1, w1, a1, b1, h1⟩ := ih1 l
    obtain ⟨S2, w2, a2, b2, h2⟩ := ih2 l
    exact ⟨0 + S1 + S2, _, .loopNext cut a1 again a2, .loopNext cut b1 again b2, by first | omega | (simp only [surOnly]; omega)⟩
  | loopBreak cut _ ih =>
    intro l; obtain ⟨S, w', a, b, h⟩ := ih l
    exact ⟨0 + S, _, .loopBreak cut a, .loopBreak cut b, by first | omega | (simp only [surOnly]; omega)⟩
  | loopExit cut _ stop ih =>
    intro l; obtain ⟨S, w', a, b, h⟩ := ih l
    exact ⟨0 + S, _, .loopExit cut a stop, .loopExit cut b stop, by first | omega | (simp only [surOnly]; omega)⟩
  | loopCut stopped =>
    intro l; exact ⟨0, _, .loopCut (lp := surOnly lp) stopped, .loopCut stopped, by first | omega | (simp only [surOnly]; omega)⟩
  | @callShort s returns target arguments handler output short run =>
    intro l
    refine ⟨_, _, .callShort (lp := surOnly lp) short run, .callShort short run, ?_⟩
    simp only [surOnly]
    rcases returns with _ | ⟨names, live⟩ <;> simp only <;> omega
  | @callTail s target arguments handler values env prog result post wb args find noHandler clock _ ih =>
    intro l
    obtain ⟨S, w', a, b, h⟩ := ih (calleeName target values, 2)
    exact ⟨_, _, .callTail args find noHandler clock a, .callTail args find noHandler clock b,
      by first | omega | (simp only [surOnly]; omega)⟩
  | @callRet s names live target arguments handler values env prog entry result post wb args find nodup cut _
      plain ih =>
    intro l
    obtain ⟨S, w', a, b, h⟩ := ih (calleeName target values, 2)
    exact ⟨_, _, .callRet args find nodup cut a plain, .callRet args find nodup cut b plain,
      by first | omega | (simp only [surOnly]; omega)⟩
  | @callRetCont s names live target arguments exceptionName handlerProgram continuation liveOut values env prog
      entry returned post wb output wc args find nodup cut _ lengths _ ih1 ih2 =>
    intro l
    obtain ⟨S1, w1, a1, b1, h1⟩ := ih1 (calleeName target values, 2)
    obtain ⟨S2, w2, a2, b2, h2⟩ := ih2 (labAfter handlerProgram (l.1, l.2 + 1))
    exact ⟨_, _, .callRetCont (exceptionName := exceptionName) (liveOut := liveOut) args find nodup cut a1 lengths a2,
      .callRetCont (exceptionName := exceptionName) (liveOut := liveOut) args find nodup cut b1 lengths b2,
      by first | omega | (simp only [surOnly]; omega)⟩
  | @callHandle s names live target arguments exceptionName handlerProgram continuation liveOut values env prog
      entry exn post wb output wh args find nodup cut _ _ ih1 ih2 =>
    intro l
    obtain ⟨S1, w1, a1, b1, h1⟩ := ih1 (calleeName target values, 2)
    obtain ⟨S2, w2, a2, b2, h2⟩ := ih2 (l.1, l.2 + 1)
    exact ⟨_, _, .callHandle (continuation := continuation) (liveOut := liveOut) args find nodup cut a1 a2,
      .callHandle (continuation := continuation) (liveOut := liveOut) args find nodup cut b1 b2,
      by first | omega | (simp only [surOnly]; omega)⟩

#print axioms LoopWorkP.relabel
end InitECandidate.Runtime.FineCost
