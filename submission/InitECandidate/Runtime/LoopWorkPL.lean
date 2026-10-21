import InitECandidate.Runtime.SourceCostLoopWorkP
import InitECandidate.Runtime.LoopWordPLLabels
namespace InitECandidate.Runtime.FineCost
open Flapjack Flapjack.LoopSemStateFiniteExact

/-! Label-indexed executed Loop work. Every judgment carries the static
compiler label `l` at which `LoopToWord.compHOL` compiles the statement, so a
returning call can be charged by its Word return label; callee bodies run at
`(calleeName target values, 2)`. -/

/-- Loop prices plus label-indexed call surcharges (in Word price units). -/
structure LoopPriceL where
  base : LoopPrice
  site : Nat × Nat → Nat
  tail : Option Nat → Nat
  /-- Charged at every returning call by its number of return names. -/
  retNames : Nat → Nat

inductive LoopWorkPL (lp : LoopPriceL) {F : Type} : Nat × Nat → LoopSemStateFiniteExact 64 F → HolLoopProg 64 →
    (Option (LoopResultExact 64) × LoopSemStateFiniteExact 64 F) → Nat → Prop where
  | atom {l s p output cost} (leaf : lp.base.leaf p = some cost)
      (run : evaluate p s = output) : LoopWorkPL lp l s p output cost
  | mark {l s p output w} (inner : LoopWorkPL lp l s p output w) : LoopWorkPL lp l s (.mark p) output w
  | seqNext {l s first second middle output a b}
      (one : LoopWorkPL lp l s first (none, middle) a) (two : LoopWorkPL lp (labAfter first l) middle second output b) :
      LoopWorkPL lp l s (.seq first second) output (a + b)
  | seqStop {l s first second result post a} (one : LoopWorkPL lp l s first (some result, post) a) :
      LoopWorkPL lp l s (.seq first second) (some result, post) a
  | iteBranch {l s operator register right yes no live x y output w}
      (lhs : sptLookup register s.locals = some (.word x))
      (rhs : LoopSemStateFiniteExact.getVarImm right s = some (.word y))
      (branch : LoopWorkPL lp (if Compiler.Encoders.Asm.wordCmpHOL operator x y then l else labAfter yes l) s
        (if Compiler.Encoders.Asm.wordCmpHOL operator x y then yes else no) output w) :
      LoopWorkPL lp l s (.ite operator register right yes no live) (LoopSemStateFiniteExact.cutRes live output)
        (lp.base.ite + w)
  | iteInvalid {l s operator register right yes no live}
      (invalid : ¬ ∃ x y, sptLookup register s.locals = some (.word x) ∧
        LoopSemStateFiniteExact.getVarImm right s = some (.word y)) :
      LoopWorkPL lp l s (.ite operator register right yes no live) (some .error, s) 1
  | loopNext {l s liveIn body liveOut entry result middle output wb wr}
      (cut : LoopSemStateFiniteExact.cutRes liveIn (none, s) = (none, entry))
      (one : LoopWorkPL lp l entry body (result, middle) wb)
      (again : result = none ∨ result = some (.continue 0))
      (rest : LoopWorkPL lp l middle (.loop liveIn body liveOut) output wr) :
      LoopWorkPL lp l s (.loop liveIn body liveOut) output (lp.base.iter + wb + wr)
  | loopBreak {l s liveIn body liveOut entry middle wb}
      (cut : LoopSemStateFiniteExact.cutRes liveIn (none, s) = (none, entry))
      (one : LoopWorkPL lp l entry body (some (.break 0), middle) wb) :
      LoopWorkPL lp l s (.loop liveIn body liveOut) (LoopSemStateFiniteExact.cutRes liveOut (none, middle))
        (lp.base.iter + wb)
  | loopExit {l s liveIn body liveOut entry result middle wb}
      (cut : LoopSemStateFiniteExact.cutRes liveIn (none, s) = (none, entry))
      (one : LoopWorkPL lp l entry body (result, middle) wb)
      (stop : result ≠ none ∧ result ≠ some (.continue 0) ∧ result ≠ some (.break 0)) :
      LoopWorkPL lp l s (.loop liveIn body liveOut) (LoopSemStateFiniteExact.exitLoop result, middle)
        (lp.base.iter + wb)
  | loopCut {l s liveIn body liveOut result cut}
      (stopped : LoopSemStateFiniteExact.cutRes liveIn (none, s) = (some result, cut)) :
      LoopWorkPL lp l s (.loop liveIn body liveOut) (some result, cut) lp.base.iter
  | callShort {l s returns target arguments handler output}
      (short : loopCallShort s returns target arguments handler)
      (run : evaluate (.call returns target arguments handler) s = output) :
      LoopWorkPL lp l s (.call returns target arguments handler) output
        (lp.base.call + lp.base.argCost arguments.length +
          (match returns with | some (names, _) => lp.site l + lp.retNames names.length | none => lp.tail target))
  | callTail {l s target arguments handler values env prog result post wb}
      (args : LoopSemStateFiniteExact.getVars arguments s = some values)
      (find : LoopSemStateFiniteExact.findCode target values s.code = some (env, prog))
      (noHandler : handler.isSome = false) (clock : s.clock ≠ 0)
      (body : LoopWorkPL lp (calleeName target values, 2) { LoopSemStateFiniteExact.decClock s with locals := env }
        prog (result, post) wb) :
      LoopWorkPL lp l s (.call none target arguments handler) (loopTailExit result post)
        (lp.base.call + lp.base.argCost arguments.length + lp.tail target + wb)
  | callRet {l s names live target arguments handler values env prog entry result post wb}
      (args : LoopSemStateFiniteExact.getVars arguments s = some values)
      (find : LoopSemStateFiniteExact.findCode target values s.code = some (env, prog))
      (nodup : names.Nodup) (cut : LoopSemStateFiniteExact.cutRes live (none, s) = (none, entry))
      (body : LoopWorkPL lp (calleeName target values, 2) { entry with locals := env } prog (result, post) wb)
      (plain : loopRetPlain result names handler) :
      LoopWorkPL lp l s (.call (some (names, live)) target arguments handler)
        (loopRetExit result post entry names)
        (lp.base.call + lp.base.argCost arguments.length + lp.site l + lp.retNames names.length + wb + lp.base.ret * loopRetWords result)
  | callRetCont {l s names live target arguments exceptionName handlerProgram continuation
      liveOut values env prog entry returned post wb output wc}
      (args : LoopSemStateFiniteExact.getVars arguments s = some values)
      (find : LoopSemStateFiniteExact.findCode target values s.code = some (env, prog))
      (nodup : names.Nodup) (cut : LoopSemStateFiniteExact.cutRes live (none, s) = (none, entry))
      (body : LoopWorkPL lp (calleeName target values, 2) { entry with locals := env } prog
        (some (.result returned), post) wb)
      (lengths : returned.length = names.length)
      (cont : LoopWorkPL lp (labAfter handlerProgram (l.1, l.2 + 1))
        (LoopSemStateFiniteExact.setVars names returned { post with locals := entry.locals })
        continuation output wc) :
      LoopWorkPL lp l s (.call (some (names, live)) target arguments
          (some (exceptionName, handlerProgram, continuation, liveOut)))
        (LoopSemStateFiniteExact.cutRes liveOut output)
        (lp.base.call + lp.base.cont + lp.base.argCost arguments.length + lp.site l + lp.retNames names.length + wb +
          lp.base.ret * returned.length + wc)
  | callHandle {l s names live target arguments exceptionName handlerProgram continuation
      liveOut values env prog entry exn post wb output wh}
      (args : LoopSemStateFiniteExact.getVars arguments s = some values)
      (find : LoopSemStateFiniteExact.findCode target values s.code = some (env, prog))
      (nodup : names.Nodup) (cut : LoopSemStateFiniteExact.cutRes live (none, s) = (none, entry))
      (body : LoopWorkPL lp (calleeName target values, 2) { entry with locals := env } prog
        (some (.exception exn), post) wb)
      (handle : LoopWorkPL lp (l.1, l.2 + 1)
        (LoopSemStateFiniteExact.setVar exceptionName exn { post with locals := entry.locals })
        handlerProgram output wh) :
      LoopWorkPL lp l s (.call (some (names, live)) target arguments
          (some (exceptionName, handlerProgram, continuation, liveOut)))
        (LoopSemStateFiniteExact.cutRes liveOut output)
        (lp.base.call + lp.base.cont + lp.base.argCost arguments.length + lp.site l + lp.retNames names.length + wb + wh)

/-- Forgetting labels and surcharges gives a `LoopWorkP` run (so soundness and
every unlabeled fact carry over). -/
theorem LoopWorkPL.toP {F : Type} {lp : LoopPriceL} {l} {s : LoopSemStateFiniteExact 64 F} {p : HolLoopProg 64}
    {output} {w : Nat} (work : LoopWorkPL lp l s p output w) : ∃ w', w' ≤ w ∧ LoopWorkP lp.base s p output w' := by
  induction work with
  | atom leaf run => exact ⟨_, Nat.le_refl _, .atom leaf run⟩
  | mark inner ih => obtain ⟨w', h, i⟩ := ih; exact ⟨w', h, .mark i⟩
  | seqNext one two ih1 ih2 =>
    obtain ⟨a', h1, i1⟩ := ih1; obtain ⟨b', h2, i2⟩ := ih2; exact ⟨a' + b', by omega, .seqNext i1 i2⟩
  | seqStop one ih => obtain ⟨a', h, i⟩ := ih; exact ⟨a', h, .seqStop i⟩
  | iteBranch lhs rhs branch ih => obtain ⟨w', h, i⟩ := ih; exact ⟨_, by omega, .iteBranch lhs rhs i⟩
  | iteInvalid invalid => exact ⟨1, Nat.le_refl _, .iteInvalid invalid⟩
  | loopNext cut one again rest ih1 ih2 =>
    obtain ⟨a', h1, i1⟩ := ih1; obtain ⟨b', h2, i2⟩ := ih2; exact ⟨_, by omega, .loopNext cut i1 again i2⟩
  | loopBreak cut one ih => obtain ⟨w', h, i⟩ := ih; exact ⟨_, by omega, .loopBreak cut i⟩
  | loopExit cut one stop ih => obtain ⟨w', h, i⟩ := ih; exact ⟨_, by omega, .loopExit cut i stop⟩
  | loopCut stopped => exact ⟨_, Nat.le_refl _, .loopCut stopped⟩
  | callShort short run => exact ⟨_, by omega, .callShort short run⟩
  | callTail args find noHandler clock body ih =>
    obtain ⟨w', h, i⟩ := ih; exact ⟨_, by omega, .callTail args find noHandler clock i⟩
  | callRet args find nodup cut body plain ih =>
    obtain ⟨w', h, i⟩ := ih; exact ⟨_, by omega, .callRet args find nodup cut i plain⟩
  | callRetCont args find nodup cut body lengths cont ih1 ih2 =>
    obtain ⟨a', h1, i1⟩ := ih1; obtain ⟨b', h2, i2⟩ := ih2
    exact ⟨_, by omega, .callRetCont args find nodup cut i1 lengths i2⟩
  | callHandle args find nodup cut body handle ih1 ih2 =>
    obtain ⟨a', h1, i1⟩ := ih1; obtain ⟨b', h2, i2⟩ := ih2
    exact ⟨_, by omega, .callHandle args find nodup cut i1 i2⟩

theorem LoopWorkPL.sound {F : Type} {lp : LoopPriceL} {l} {s : LoopSemStateFiniteExact 64 F} {p : HolLoopProg 64}
    {output} {w : Nat} (work : LoopWorkPL lp l s p output w) : evaluate p s = output := by
  obtain ⟨_, _, i⟩ := work.toP; exact i.sound

#print axioms LoopWorkPL.sound
end InitECandidate.Runtime.FineCost
