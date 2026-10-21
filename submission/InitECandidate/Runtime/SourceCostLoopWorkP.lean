import InitECandidate.Runtime.SourceCostLoopWork
namespace InitECandidate.Runtime.FineCost
open Flapjack Flapjack.LoopSemStateFiniteExact

/-! Price-parametric executed Loop work. `LoopWork` is the instance
`defaultLoopPrice`. -/

/-- Local Loop prices: non-recursive statements, a conditional, a loop
iteration, a call node, each argument, each returned word, and the extra unit
of a call with a continuation or handler. -/
structure LoopPrice where
  leaf : HolLoopProg 64 → Option Nat
  ite : Nat
  iter : Nat
  call : Nat
  arg : Nat
  ret : Nat
  cont : Nat

/-- The prices of `LoopWork`. -/
def defaultLoopPrice : LoopPrice where
  leaf := loopWorkLeafCost
  ite := 37
  iter := 16
  call := 189
  arg := 39
  ret := 49
  cont := 7

/-- Executed Loop work, indexed by the exact evaluator output. Every executed
statement pays its local cost; recursive rules expose only actual successors:
the selected branch, each loop iteration and the actual callee, continuation
or handler. -/
inductive LoopWorkP (lp : LoopPrice) {F : Type} : LoopSemStateFiniteExact 64 F → HolLoopProg 64 →
    (Option (LoopResultExact 64) × LoopSemStateFiniteExact 64 F) → Nat → Prop where
  | atom {s p output cost} (leaf : lp.leaf p = some cost)
      (run : evaluate p s = output) : LoopWorkP lp s p output cost
  | mark {s p output w} (inner : LoopWorkP lp s p output w) : LoopWorkP lp s (.mark p) output w
  | seqNext {s first second middle output a b}
      (one : LoopWorkP lp s first (none, middle) a) (two : LoopWorkP lp middle second output b) :
      LoopWorkP lp s (.seq first second) output (a + b)
  | seqStop {s first second result post a} (one : LoopWorkP lp s first (some result, post) a) :
      LoopWorkP lp s (.seq first second) (some result, post) a
  | iteBranch {s operator register right yes no live x y output w}
      (lhs : sptLookup register s.locals = some (.word x))
      (rhs : LoopSemStateFiniteExact.getVarImm right s = some (.word y))
      (branch : LoopWorkP lp s (if Compiler.Encoders.Asm.wordCmpHOL operator x y then yes else no)
        output w) :
      LoopWorkP lp s (.ite operator register right yes no live) (LoopSemStateFiniteExact.cutRes live output) (lp.ite + w)
  | iteInvalid {s operator register right yes no live}
      (invalid : ¬ ∃ x y, sptLookup register s.locals = some (.word x) ∧
        LoopSemStateFiniteExact.getVarImm right s = some (.word y)) :
      LoopWorkP lp s (.ite operator register right yes no live) (some .error, s) 1
  | loopNext {s liveIn body liveOut entry result middle output wb wr}
      (cut : LoopSemStateFiniteExact.cutRes liveIn (none, s) = (none, entry))
      (one : LoopWorkP lp entry body (result, middle) wb)
      (again : result = none ∨ result = some (.continue 0))
      (rest : LoopWorkP lp middle (.loop liveIn body liveOut) output wr) :
      LoopWorkP lp s (.loop liveIn body liveOut) output (lp.iter + wb + wr)
  | loopBreak {s liveIn body liveOut entry middle wb}
      (cut : LoopSemStateFiniteExact.cutRes liveIn (none, s) = (none, entry))
      (one : LoopWorkP lp entry body (some (.break 0), middle) wb) :
      LoopWorkP lp s (.loop liveIn body liveOut) (LoopSemStateFiniteExact.cutRes liveOut (none, middle)) (lp.iter + wb)
  | loopExit {s liveIn body liveOut entry result middle wb}
      (cut : LoopSemStateFiniteExact.cutRes liveIn (none, s) = (none, entry))
      (one : LoopWorkP lp entry body (result, middle) wb)
      (stop : result ≠ none ∧ result ≠ some (.continue 0) ∧ result ≠ some (.break 0)) :
      LoopWorkP lp s (.loop liveIn body liveOut) (LoopSemStateFiniteExact.exitLoop result, middle) (lp.iter + wb)
  | loopCut {s liveIn body liveOut result cut}
      (stopped : LoopSemStateFiniteExact.cutRes liveIn (none, s) = (some result, cut)) :
      LoopWorkP lp s (.loop liveIn body liveOut) (some result, cut) lp.iter
  | callShort {s returns target arguments handler output}
      (short : loopCallShort s returns target arguments handler)
      (run : evaluate (.call returns target arguments handler) s = output) :
      LoopWorkP lp s (.call returns target arguments handler) output (lp.call + lp.arg * arguments.length)
  | callTail {s target arguments handler values env prog result post wb}
      (args : LoopSemStateFiniteExact.getVars arguments s = some values)
      (find : LoopSemStateFiniteExact.findCode target values s.code = some (env, prog))
      (noHandler : handler.isSome = false) (clock : s.clock ≠ 0)
      (body : LoopWorkP lp { LoopSemStateFiniteExact.decClock s with locals := env } prog (result, post) wb) :
      LoopWorkP lp s (.call none target arguments handler) (loopTailExit result post)
        (lp.call + lp.arg * arguments.length + wb)
  | callRet {s names live target arguments handler values env prog entry result post wb}
      (args : LoopSemStateFiniteExact.getVars arguments s = some values)
      (find : LoopSemStateFiniteExact.findCode target values s.code = some (env, prog))
      (nodup : names.Nodup) (cut : LoopSemStateFiniteExact.cutRes live (none, s) = (none, entry))
      (body : LoopWorkP lp { entry with locals := env } prog (result, post) wb)
      (plain : loopRetPlain result names handler) :
      LoopWorkP lp s (.call (some (names, live)) target arguments handler)
        (loopRetExit result post entry names) (lp.call + lp.arg * arguments.length + wb + lp.ret * loopRetWords result)
  | callRetCont {s names live target arguments exceptionName handlerProgram continuation
      liveOut values env prog entry returned post wb output wc}
      (args : LoopSemStateFiniteExact.getVars arguments s = some values)
      (find : LoopSemStateFiniteExact.findCode target values s.code = some (env, prog))
      (nodup : names.Nodup) (cut : LoopSemStateFiniteExact.cutRes live (none, s) = (none, entry))
      (body : LoopWorkP lp { entry with locals := env } prog (some (.result returned), post) wb)
      (lengths : returned.length = names.length)
      (cont : LoopWorkP lp (LoopSemStateFiniteExact.setVars names returned { post with locals := entry.locals })
        continuation output wc) :
      LoopWorkP lp s (.call (some (names, live)) target arguments
          (some (exceptionName, handlerProgram, continuation, liveOut)))
        (LoopSemStateFiniteExact.cutRes liveOut output) (lp.call + lp.cont + lp.arg * arguments.length + wb + lp.ret * returned.length + wc)
  | callHandle {s names live target arguments exceptionName handlerProgram continuation
      liveOut values env prog entry exn post wb output wh}
      (args : LoopSemStateFiniteExact.getVars arguments s = some values)
      (find : LoopSemStateFiniteExact.findCode target values s.code = some (env, prog))
      (nodup : names.Nodup) (cut : LoopSemStateFiniteExact.cutRes live (none, s) = (none, entry))
      (body : LoopWorkP lp { entry with locals := env } prog (some (.exception exn), post) wb)
      (handle : LoopWorkP lp (LoopSemStateFiniteExact.setVar exceptionName exn { post with locals := entry.locals })
        handlerProgram output wh) :
      LoopWorkP lp s (.call (some (names, live)) target arguments
          (some (exceptionName, handlerProgram, continuation, liveOut)))
        (LoopSemStateFiniteExact.cutRes liveOut output) (lp.call + lp.cont + lp.arg * arguments.length + wb + wh)

theorem LoopWorkP.sound {F : Type} {s : LoopSemStateFiniteExact 64 F} {p : HolLoopProg 64}
    {output} {w : Nat} {lp : LoopPrice} (work : LoopWorkP lp s p output w) : evaluate p s = output := by
  induction work with
  | atom leaf run => exact run
  | mark inner ih => rw [evaluate]; exact ih
  | seqNext one two ihOne ihTwo => rw [evaluate_seq, ihOne]; exact ihTwo
  | seqStop one ih => rw [evaluate_seq, ih]
  | @iteBranch s operator register right yes no live x y output w lhs rhs branch ih =>
    rw [evaluate, lhs, rhs]
    simp only []
    split <;> simp_all
  | iteInvalid invalid =>
    rw [evaluate]
    split
    · rename_i x y hx hy
      exact False.elim (invalid ⟨x, y, hx, hy⟩)
    · rfl
  | @loopNext s liveIn body liveOut entry result middle output wb wr cut one again rest ihOne
      ihRest =>
    rw [evaluate]
    split
    · rename_i s1 hc
      rw [cut] at hc
      simp only [Prod.mk.injEq, true_and] at hc
      subst hc
      rw [fix_clock_evaluate, ihOne]
      rcases again with rfl | rfl
      · exact ihRest
      · exact ihRest
    · rename_i hnot
      exact (hnot _ cut).elim
  | @loopBreak s liveIn body liveOut entry middle wb cut one ihOne =>
    rw [evaluate]
    split
    · rename_i s1 hc
      rw [cut] at hc
      simp only [Prod.mk.injEq, true_and] at hc
      subst hc
      rw [fix_clock_evaluate, ihOne]
      rfl
    · rename_i hnot
      exact (hnot _ cut).elim
  | @loopExit s liveIn body liveOut entry result middle wb cut one stop ihOne =>
    rw [evaluate]
    split
    · rename_i s1 hc
      rw [cut] at hc
      simp only [Prod.mk.injEq, true_and] at hc
      subst hc
      rw [fix_clock_evaluate, ihOne]
      obtain ⟨n1, n2, n3⟩ := stop
      rcases result with _ | r
      · exact absurd rfl n1
      · cases r with
        | «continue» n => cases n with
          | zero => exact absurd rfl n2
          | succ n => rfl
        | «break» n => cases n with
          | zero => exact absurd rfl n3
          | succ n => rfl
        | _ => rfl
    · rename_i hnot
      exact (hnot _ cut).elim
  | @loopCut s liveIn body liveOut result cut stopped =>
    rw [evaluate]
    split
    · rename_i s1 hc
      rw [stopped] at hc
      simp at hc
    · exact stopped
  | callShort short run => exact run
  | @callTail s target arguments handler values env prog result post wb args find noHandler
      clock body ih =>
    rw [evaluate, args]
    simp only []
    rw [find]
    simp only [noHandler, Bool.false_eq_true, if_false, clock, dite_false]
    rw [ih]
    rcases result with _ | (_ | _ | _ | _ | _ | _ | _) <;> rfl
  | @callRet s names live target arguments handler values env prog entry result post wb args find
      nodup cut body plain ih =>
    rw [evaluate, args]
    simp only []
    rw [find]
    simp only [nodup, not_true_eq_false, if_false]
    split
    · rename_i s1 hc
      rw [cut] at hc
      simp only [Prod.mk.injEq, true_and] at hc
      subst hc
      rw [fix_clock_evaluate, ih]
      rcases result with _ | r
      · rfl
      cases r with
      | result vs =>
        simp only [loopRetExit]
        by_cases hlen : vs.length ≠ names.length
        · simp [hlen]
        · simp only [hlen, if_false]
          cases handler with
          | none => rfl
          | some h =>
            simp only [loopRetPlain] at plain
            exact absurd plain hlen
      | exception exn =>
        cases handler with
        | none => rfl
        | some h => simp [loopRetPlain] at plain
      | _ => rfl
    · rename_i hnot
      exact (hnot _ cut).elim
  | @callRetCont s names live target arguments exceptionName handlerProgram continuation liveOut
      values env prog entry returned post wb output wc args find nodup cut body lengths cont
      ihBody ihCont =>
    rw [evaluate, args]
    simp only []
    rw [find]
    simp only [nodup, not_true_eq_false, if_false]
    split
    · rename_i s1 hc
      rw [cut] at hc
      simp only [Prod.mk.injEq, true_and] at hc
      subst hc
      rw [fix_clock_evaluate, ihBody]
      simp only [lengths, ne_eq, not_true_eq_false, if_false]
      rw [ihCont]
    · rename_i hnot
      exact (hnot _ cut).elim
  | @callHandle s names live target arguments exceptionName handlerProgram continuation liveOut
      values env prog entry exn post wb output wh args find nodup cut body handle ihBody
      ihHandle =>
    rw [evaluate, args]
    simp only []
    rw [find]
    simp only [nodup, not_true_eq_false, if_false]
    split
    · rename_i s1 hc
      rw [cut] at hc
      simp only [Prod.mk.injEq, true_and] at hc
      subst hc
      rw [fix_clock_evaluate, ihBody]
      simp only []
      rw [ihHandle]
    · rename_i hnot
      exact (hnot _ cut).elim

#print axioms LoopWorkP.sound
end InitECandidate.Runtime.FineCost
