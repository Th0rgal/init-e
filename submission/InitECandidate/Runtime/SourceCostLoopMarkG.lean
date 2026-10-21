import InitECandidate.Runtime.SourceCostLoopWorkG
import Flapjack.Pancake.LoopLive
import Flapjack.Pancake.Proofs.LoopLive.Optimise
namespace InitECandidate.Runtime.FineCost
open Flapjack Flapjack.LoopSemStateFiniteExact

variable {L : LeafPrice}

private theorem marked_shortG {F : Type} (s : LoopSemStateFiniteExact 64 F)
    (returns : Option (List Nat × NumSet)) (target : Option Nat) (arguments : List Nat)
    (handler : Option (Nat × HolLoopProg 64 × HolLoopProg 64 × NumSet)) :
    loopCallShort s returns target arguments handler →
      loopCallShort s returns target arguments
        (handler.map (fun (exn, body, cont, live) =>
          (exn, (markAllHOL body).1, (markAllHOL cont).1, live))) := by
  intro short
  simpa only [loopCallShort, Option.isSome_map] using short

/-- The actual `mark_all` pass preserves the exact executed Loop work, including
chosen branches, each iteration, and reached call handlers/continuations.
Marks add no work; code-table callees themselves are unchanged by this pass. -/
theorem LoopWorkG.mark_all {F : Type} {s : LoopSemStateFiniteExact 64 F}
    {p : HolLoopProg 64} {output} {w : Nat} (work : LoopWorkG L s p output w) :
    LoopWorkG L s (markAllHOL p).1 output w := by
  induction work with
  | @atom s p output cost leaf run =>
    have original := leaf
    have leaf := L.dom _ _ leaf
    cases p <;> simp [loopWorkLeafCost] at leaf
    all_goals try contradiction
    all_goals simp only [markAllHOL]
    all_goals exact LoopWorkG.mark (LoopWorkG.atom original run)
  | mark inner ih => simpa only [markAllHOL] using ih
  | seqNext one two ihOne ihTwo =>
    simp only [markAllHOL]
    split
    · exact LoopWorkG.mark (LoopWorkG.seqNext ihOne ihTwo)
    · exact LoopWorkG.seqNext ihOne ihTwo
  | seqStop one ih =>
    simp only [markAllHOL]
    split
    · exact LoopWorkG.mark (LoopWorkG.seqStop ih)
    · exact LoopWorkG.seqStop ih
  | @iteBranch s operator register right yes no live x y output w lhs rhs branch ih =>
    have chosen : LoopWorkG L s
        (if Compiler.Encoders.Asm.wordCmpHOL operator x y then
          (markAllHOL yes).1 else (markAllHOL no).1) output w := by
      split <;> simpa only [*, Bool.false_eq_true, ↓reduceIte] using ih
    have run := LoopWorkG.iteBranch (live := live) lhs rhs chosen
    simp only [markAllHOL]
    split
    · exact LoopWorkG.mark run
    · exact run
  | iteInvalid invalid =>
    simp only [markAllHOL]
    split
    · exact LoopWorkG.mark (LoopWorkG.iteInvalid invalid)
    · exact LoopWorkG.iteInvalid invalid
  | loopNext cut one again rest ihOne ihRest =>
    simp only [markAllHOL] at ihRest ⊢
    exact LoopWorkG.loopNext cut ihOne again ihRest
  | loopBreak cut one ihOne =>
    simp only [markAllHOL]
    exact LoopWorkG.loopBreak cut ihOne
  | loopExit cut one stop ihOne =>
    simp only [markAllHOL]
    exact LoopWorkG.loopExit cut ihOne stop
  | loopCut stopped =>
    simp only [markAllHOL]
    exact LoopWorkG.loopCut stopped
  | @callShort s returns target arguments handler output short run =>
    have markedRun : evaluate
        (.call returns target arguments
          (handler.map (fun (exn, body, cont, live) =>
            (exn, (markAllHOL body).1, (markAllHOL cont).1, live)))) s = output := by
      cases handler with
      | none => simpa only [Option.map_none] using run
      | some handler =>
        rcases handler with ⟨exn, body, cont, live⟩
        have semantic := Flapjack.mark_correct
          (.call returns target arguments (some (exn, body, cont, live))) s
          output.1 output.2 run
        simp only [markAllHOL] at semantic
        split at semantic
        · simpa only [evaluate, Option.map_some] using semantic
        · simpa only [Option.map_some] using semantic
    have core := LoopWorkG.callShort (L := L) (marked_shortG s returns target arguments handler short) markedRun
    cases handler with
    | none => simpa only [markAllHOL, Option.map_none] using LoopWorkG.mark core
    | some handler =>
      rcases handler with ⟨exn, body, cont, live⟩
      simp only [markAllHOL]
      split
      · exact LoopWorkG.mark core
      · exact core
  | @callTail s target arguments handler values env prog result post wb args find noHandler
      clock body ih =>
    have noneHandler : handler = none := by cases handler <;> simp_all
    subst handler
    simp only [markAllHOL]
    exact LoopWorkG.mark (LoopWorkG.callTail args find noHandler clock body)
  | @callRet s names live target arguments handler values env prog entry result post wb args find
      nodup cut body plain ih =>
    cases handler with
    | none =>
      simp only [markAllHOL]
      exact LoopWorkG.mark (LoopWorkG.callRet args find nodup cut body plain)
    | some handler =>
      rcases handler with ⟨exn, handlerBody, cont, liveOut⟩
      have plain' : loopRetPlain result names
          (some (exn, (markAllHOL handlerBody).1, (markAllHOL cont).1, liveOut)) := by
        cases result with
        | none => trivial
        | some result => cases result <;> exact plain
      have core := LoopWorkG.callRet args find nodup cut body plain'
      simp only [markAllHOL]
      split
      · exact LoopWorkG.mark core
      · exact core
  | @callRetCont s names live target arguments exceptionName handlerProgram continuation
      liveOut values env prog entry returned post wb output wc args find nodup cut body lengths cont
      ihBody ihCont =>
    have core := LoopWorkG.callRetCont (exceptionName := exceptionName) (liveOut := liveOut)
      (handlerProgram := (markAllHOL handlerProgram).1)
      args find nodup cut body lengths ihCont
    simp only [markAllHOL]
    split
    · exact LoopWorkG.mark core
    · exact core
  | @callHandle s names live target arguments exceptionName handlerProgram continuation
      liveOut values env prog entry exn post wb output wh args find nodup cut body handle ihBody
      ihHandle =>
    have core := LoopWorkG.callHandle (liveOut := liveOut) (continuation := (markAllHOL continuation).1)
      args find nodup cut body ihHandle
    simp only [markAllHOL]
    split
    · exact LoopWorkG.mark core
    · exact core

#print axioms LoopWorkG.mark_all
end InitECandidate.Runtime.FineCost
