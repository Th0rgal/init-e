import InitECandidate.Runtime.LoopExpressionWork
import Flapjack.Pancake.Semantics.LoopProps.EvaluateClockExact
import Flapjack.Pancake.Semantics.LoopProps.NestedSeqExact
namespace InitECandidate.Runtime.FineCost
open Flapjack Flapjack.LoopSemStateFiniteExact

/-- Local cost of a non-recursive Loop statement: one dispatch unit plus the
residual expression work and moved variable counts it actually touches. -/
def loopWorkLeafCost : HolLoopProg 64 → Option Nat
  | .skip => some 0
  | .fail | .arith _ | .load32 _ _ | .loadByte _ _ | .store32 _ _ | .storeByte _ _
  | .break _ | .continue _ | .raise _ | .tick | .locValue _ _ | .ffi _ _ _ _ _ _ => some 1
  | .assign _ value | .store value _ | .setGlobal _ value | .shMem _ _ value =>
      some (1 + loopValueWork value)
  | .primitive destinations _ arguments => some (1 + destinations.length + arguments.length)
  | .return values => some (1 + values.length)
  | _ => none

/-- Output of a tail call after the callee body. -/
def loopTailExit {F : Type} : Option (LoopResultExact 64) → LoopSemStateFiniteExact 64 F →
    Option (LoopResultExact 64) × LoopSemStateFiniteExact 64 F
  | none, post => (some .error, post)
  | some (.continue _), post => (some .error, post)
  | some (.break _), post => (some .error, post)
  | some result, post => (some result, post)

/-- Callee exits of a returning call that do not run a continuation program. -/
def loopRetPlain (result : Option (LoopResultExact 64)) (names : List Nat)
    (handler : Option (Nat × HolLoopProg 64 × HolLoopProg 64 × NumSet)) : Prop :=
  match result, handler with
  | some (.result values), some _ => values.length ≠ names.length
  | some (.exception _), some _ => False
  | _, _ => True

def loopRetExit {F : Type} (result : Option (LoopResultExact 64))
    (post caller : LoopSemStateFiniteExact 64 F) (names : List Nat) :
    Option (LoopResultExact 64) × LoopSemStateFiniteExact 64 F :=
  match result with
  | some (.result values) =>
      if values.length ≠ names.length then (some .error, post)
      else (none, LoopSemStateFiniteExact.setVars names values { post with locals := caller.locals })
  | some (.exception exn) => (some (.exception exn), { post with locals := .ln })
  | some (.continue _) | some (.break _) | none => (some .error, post)
  | result => (result, post)

def loopRetWords : Option (LoopResultExact 64) → Nat
  | some (.result values) => values.length
  | _ => 0

/-- A call that stops before its callee body runs. -/
def loopCallShort {F : Type} (s : LoopSemStateFiniteExact 64 F)
    (returns : Option (List Nat × NumSet)) (target : Option Nat) (arguments : List Nat)
    (handler : Option (Nat × HolLoopProg 64 × HolLoopProg 64 × NumSet)) : Prop :=
  LoopSemStateFiniteExact.getVars arguments s = none ∨ ∃ values, LoopSemStateFiniteExact.getVars arguments s = some values ∧
    (LoopSemStateFiniteExact.findCode target values s.code = none ∨ ∃ env prog,
      LoopSemStateFiniteExact.findCode target values s.code = some (env, prog) ∧
      ((returns = none ∧ (handler.isSome = true ∨ s.clock = 0)) ∨
        ∃ names live, returns = some (names, live) ∧
          (¬ names.Nodup ∨ ∃ result cut, LoopSemStateFiniteExact.cutRes live (none, s) = (some result, cut))))

/-- Executed Loop work, indexed by the exact evaluator output. Every executed
statement pays its local cost; recursive rules expose only actual successors:
the selected branch, each loop iteration and the actual callee, continuation
or handler. -/
inductive LoopWork {F : Type} : LoopSemStateFiniteExact 64 F → HolLoopProg 64 →
    (Option (LoopResultExact 64) × LoopSemStateFiniteExact 64 F) → Nat → Prop where
  | atom {s p output cost} (leaf : loopWorkLeafCost p = some cost)
      (run : evaluate p s = output) : LoopWork s p output cost
  | mark {s p output w} (inner : LoopWork s p output w) : LoopWork s (.mark p) output w
  | seqNext {s first second middle output a b}
      (one : LoopWork s first (none, middle) a) (two : LoopWork middle second output b) :
      LoopWork s (.seq first second) output (a + b)
  | seqStop {s first second result post a} (one : LoopWork s first (some result, post) a) :
      LoopWork s (.seq first second) (some result, post) a
  | iteBranch {s operator register right yes no live x y output w}
      (lhs : sptLookup register s.locals = some (.word x))
      (rhs : LoopSemStateFiniteExact.getVarImm right s = some (.word y))
      (branch : LoopWork s (if Compiler.Encoders.Asm.wordCmpHOL operator x y then yes else no)
        output w) :
      LoopWork s (.ite operator register right yes no live) (LoopSemStateFiniteExact.cutRes live output) (2 + w)
  | iteInvalid {s operator register right yes no live}
      (invalid : ¬ ∃ x y, sptLookup register s.locals = some (.word x) ∧
        LoopSemStateFiniteExact.getVarImm right s = some (.word y)) :
      LoopWork s (.ite operator register right yes no live) (some .error, s) 1
  | loopNext {s liveIn body liveOut entry result middle output wb wr}
      (cut : LoopSemStateFiniteExact.cutRes liveIn (none, s) = (none, entry))
      (one : LoopWork entry body (result, middle) wb)
      (again : result = none ∨ result = some (.continue 0))
      (rest : LoopWork middle (.loop liveIn body liveOut) output wr) :
      LoopWork s (.loop liveIn body liveOut) output (3 + wb + wr)
  | loopBreak {s liveIn body liveOut entry middle wb}
      (cut : LoopSemStateFiniteExact.cutRes liveIn (none, s) = (none, entry))
      (one : LoopWork entry body (some (.break 0), middle) wb) :
      LoopWork s (.loop liveIn body liveOut) (LoopSemStateFiniteExact.cutRes liveOut (none, middle)) (3 + wb)
  | loopExit {s liveIn body liveOut entry result middle wb}
      (cut : LoopSemStateFiniteExact.cutRes liveIn (none, s) = (none, entry))
      (one : LoopWork entry body (result, middle) wb)
      (stop : result ≠ none ∧ result ≠ some (.continue 0) ∧ result ≠ some (.break 0)) :
      LoopWork s (.loop liveIn body liveOut) (LoopSemStateFiniteExact.exitLoop result, middle) (3 + wb)
  | loopCut {s liveIn body liveOut result cut}
      (stopped : LoopSemStateFiniteExact.cutRes liveIn (none, s) = (some result, cut)) :
      LoopWork s (.loop liveIn body liveOut) (some result, cut) 3
  | callShort {s returns target arguments handler output}
      (short : loopCallShort s returns target arguments handler)
      (run : evaluate (.call returns target arguments handler) s = output) :
      LoopWork s (.call returns target arguments handler) output (1 + arguments.length)
  | callTail {s target arguments handler values env prog result post wb}
      (args : LoopSemStateFiniteExact.getVars arguments s = some values)
      (find : LoopSemStateFiniteExact.findCode target values s.code = some (env, prog))
      (noHandler : handler.isSome = false) (clock : s.clock ≠ 0)
      (body : LoopWork { LoopSemStateFiniteExact.decClock s with locals := env } prog (result, post) wb) :
      LoopWork s (.call none target arguments handler) (loopTailExit result post)
        (1 + arguments.length + wb)
  | callRet {s names live target arguments handler values env prog entry result post wb}
      (args : LoopSemStateFiniteExact.getVars arguments s = some values)
      (find : LoopSemStateFiniteExact.findCode target values s.code = some (env, prog))
      (nodup : names.Nodup) (cut : LoopSemStateFiniteExact.cutRes live (none, s) = (none, entry))
      (body : LoopWork { entry with locals := env } prog (result, post) wb)
      (plain : loopRetPlain result names handler) :
      LoopWork s (.call (some (names, live)) target arguments handler)
        (loopRetExit result post entry names) (1 + arguments.length + wb + loopRetWords result)
  | callRetCont {s names live target arguments exceptionName handlerProgram continuation
      liveOut values env prog entry returned post wb output wc}
      (args : LoopSemStateFiniteExact.getVars arguments s = some values)
      (find : LoopSemStateFiniteExact.findCode target values s.code = some (env, prog))
      (nodup : names.Nodup) (cut : LoopSemStateFiniteExact.cutRes live (none, s) = (none, entry))
      (body : LoopWork { entry with locals := env } prog (some (.result returned), post) wb)
      (lengths : returned.length = names.length)
      (cont : LoopWork (LoopSemStateFiniteExact.setVars names returned { post with locals := entry.locals })
        continuation output wc) :
      LoopWork s (.call (some (names, live)) target arguments
          (some (exceptionName, handlerProgram, continuation, liveOut)))
        (LoopSemStateFiniteExact.cutRes liveOut output) (2 + arguments.length + wb + returned.length + wc)
  | callHandle {s names live target arguments exceptionName handlerProgram continuation
      liveOut values env prog entry exn post wb output wh}
      (args : LoopSemStateFiniteExact.getVars arguments s = some values)
      (find : LoopSemStateFiniteExact.findCode target values s.code = some (env, prog))
      (nodup : names.Nodup) (cut : LoopSemStateFiniteExact.cutRes live (none, s) = (none, entry))
      (body : LoopWork { entry with locals := env } prog (some (.exception exn), post) wb)
      (handle : LoopWork (LoopSemStateFiniteExact.setVar exceptionName exn { post with locals := entry.locals })
        handlerProgram output wh) :
      LoopWork s (.call (some (names, live)) target arguments
          (some (exceptionName, handlerProgram, continuation, liveOut)))
        (LoopSemStateFiniteExact.cutRes liveOut output) (2 + arguments.length + wb + wh)

theorem LoopWork.sound {F : Type} {s : LoopSemStateFiniteExact 64 F} {p : HolLoopProg 64}
    {output} {w : Nat} (work : LoopWork s p output w) : evaluate p s = output := by
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

#print axioms LoopWork.sound

theorem loopTailExit_add_clock {F : Type} (result : Option (LoopResultExact 64))
    (post : LoopSemStateFiniteExact 64 F) (k : Nat) :
    loopTailExit result { post with clock := post.clock + k } =
      ((loopTailExit result post).1,
        { (loopTailExit result post).2 with clock := (loopTailExit result post).2.clock + k }) := by
  rcases result with _ | r
  · rfl
  · cases r <;> rfl

theorem loopRetExit_add_clock {F : Type} (result : Option (LoopResultExact 64))
    (post entry : LoopSemStateFiniteExact 64 F) (names : List Nat) (k : Nat) :
    loopRetExit result { post with clock := post.clock + k } { entry with clock := entry.clock + k }
        names =
      ((loopRetExit result post entry names).1,
        { (loopRetExit result post entry names).2 with
          clock := (loopRetExit result post entry names).2.clock + k }) := by
  rcases result with _ | r
  · rfl
  · cases r with
    | result vs =>
      simp only [loopRetExit]
      split <;> rfl
    | _ => rfl

/-- Raising the clock does not change the work of a run that does not time
out: every sub-run on the executed path is then also non-timeout. -/
theorem LoopWork.add_clock {F : Type} {s : LoopSemStateFiniteExact 64 F} {p : HolLoopProg 64}
    {output : Option (LoopResultExact 64) × LoopSemStateFiniteExact 64 F} {w : Nat}
    (work : LoopWork s p output w) (k : Nat) (notTimeout : output.1 ≠ some .timeOut) :
    LoopWork { s with clock := s.clock + k } p
      (output.1, { output.2 with clock := output.2.clock + k }) w := by
  induction work with
  | @atom s p output cost leaf run =>
    refine LoopWork.atom leaf ?_
    exact evaluate_add_clock_eq p s output.1 output.2 k run notTimeout
  | mark inner ih => exact LoopWork.mark (ih notTimeout)
  | seqNext one two ihOne ihTwo =>
    exact LoopWork.seqNext (ihOne (by simp)) (ihTwo notTimeout)
  | seqStop one ih => exact LoopWork.seqStop (ih notTimeout)
  | @iteBranch s operator register right yes no live x y output w lhs rhs branch ih =>
    have childOk : output.1 ≠ some .timeOut := by
      intro h
      apply notTimeout
      obtain ⟨r, st⟩ := output
      simp only at h
      subst h
      simp [LoopSemStateFiniteExact.cutRes]
    have child := ih childOk
    have cut := LoopSemStateFiniteExact.cutRes_add_clock live output.1 output.2
      (LoopSemStateFiniteExact.cutRes live output).2 (LoopSemStateFiniteExact.cutRes live output).1
      k rfl notTimeout
    have rule := LoopWork.iteBranch (s := { s with clock := s.clock + k }) (live := live) lhs
      (by rw [LoopSemStateFiniteExact.getVarImm_upd_clock]; exact rhs) child
    rw [cut] at rule
    exact rule
  | @iteInvalid s operator register right yes no live invalid =>
    refine LoopWork.iteInvalid ?_
    rw [LoopSemStateFiniteExact.getVarImm_upd_clock]
    exact invalid
  | @loopNext s liveIn body liveOut entry result middle output wb wr cut one again rest ihOne
      ihRest =>
    have cut' := LoopSemStateFiniteExact.cutRes_add_clock liveIn none s entry none k cut (by simp)
    have bodyOk : result ≠ some .timeOut := by rcases again with rfl | rfl <;> simp
    exact LoopWork.loopNext cut' (ihOne bodyOk) again (ihRest notTimeout)
  | @loopBreak s liveIn body liveOut entry middle wb cut one ihOne =>
    have cut' := LoopSemStateFiniteExact.cutRes_add_clock liveIn none s entry none k cut (by simp)
    have exit := LoopSemStateFiniteExact.cutRes_add_clock liveOut none middle
      (LoopSemStateFiniteExact.cutRes liveOut (none, middle)).2
      (LoopSemStateFiniteExact.cutRes liveOut (none, middle)).1 k rfl notTimeout
    have rule := LoopWork.loopBreak (liveOut := liveOut) cut' (ihOne (by simp))
    simp only [] at rule
    rw [exit] at rule
    exact rule
  | @loopExit s liveIn body liveOut entry result middle wb cut one stop ihOne =>
    have cut' := LoopSemStateFiniteExact.cutRes_add_clock liveIn none s entry none k cut (by simp)
    have bodyOk : result ≠ some .timeOut := by
      rintro rfl
      exact notTimeout rfl
    exact LoopWork.loopExit cut' (ihOne bodyOk) stop
  | @loopCut s liveIn body liveOut result cut stopped =>
    exact LoopWork.loopCut
      (LoopSemStateFiniteExact.cutRes_add_clock liveIn none s cut (some result) k stopped notTimeout)
  | @callShort s returns target arguments handler output short run =>
    have run' := evaluate_add_clock_eq _ s output.1 output.2 k run notTimeout
    refine LoopWork.callShort ?_ run'
    unfold loopCallShort at short ⊢
    simp only [LoopSemStateFiniteExact.getVars_upd_clock]
    rcases short with hnone | ⟨values, hvals, rest⟩
    · exact Or.inl hnone
    refine Or.inr ⟨values, hvals, ?_⟩
    rcases rest with hfind | ⟨env, prog, hfind, rest⟩
    · exact Or.inl hfind
    refine Or.inr ⟨env, prog, hfind, ?_⟩
    rcases rest with ⟨rfl, hh | hz⟩ | ⟨names, live, rfl, rest⟩
    · exact Or.inl ⟨rfl, Or.inl hh⟩
    · by_cases hh : handler.isSome = true
      · exact Or.inl ⟨rfl, Or.inl hh⟩
      · exfalso
        apply notTimeout
        rw [← run, evaluate.eq_def]
        simp only [hvals, hfind]
        simp [hh, hz]
    · by_cases hnd : names.Nodup
      · rcases rest with hnd' | ⟨result, c1, hc⟩
        · exact absurd hnd hnd'
        have resultOk : result ≠ .timeOut := by
          intro hbad
          subst hbad
          apply notTimeout
          rw [← run, evaluate.eq_def]
          simp only [hvals, hfind]
          simp only [hnd, not_true_eq_false, if_false]
          split
          · rename_i s1 hc'
            rw [hc] at hc'
            simp at hc'
          · rename_i hnot
            rw [hc]
        exact Or.inr ⟨names, live, rfl, Or.inr ⟨result, _,
          LoopSemStateFiniteExact.cutRes_add_clock live none s c1 (some result) k hc
            (by simpa using resultOk)⟩⟩
      · exact Or.inr ⟨names, live, rfl, Or.inl hnd⟩
  | @callTail s target arguments handler values env prog result post wb args find noHandler
      clock body ih =>
    have bodyOk : result ≠ some .timeOut := by
      rintro rfl
      exact notTimeout rfl
    have entry : ({ LoopSemStateFiniteExact.decClock { s with clock := s.clock + k } with
        locals := env } : LoopSemStateFiniteExact 64 F) =
        { ({ LoopSemStateFiniteExact.decClock s with locals := env } :
            LoopSemStateFiniteExact 64 F) with
          clock := ({ LoopSemStateFiniteExact.decClock s with locals := env } :
            LoopSemStateFiniteExact 64 F).clock + k } := by
      cases s
      simp only [LoopSemStateFiniteExact.decClock, LoopSemStateFiniteExact.mk.injEq, true_and,
        and_true] at clock ⊢
      omega
    have rule := LoopWork.callTail (s := { s with clock := s.clock + k })
      (by rw [LoopSemStateFiniteExact.getVars_upd_clock]; exact args) find noHandler
      (by show s.clock + k ≠ 0; omega)
      (by rw [entry]; exact ih bodyOk)
    rw [loopTailExit_add_clock] at rule
    exact rule
  | @callRet s names live target arguments handler values env prog entry result post wb args find
      nodup cut body plain ih =>
    have cut' := LoopSemStateFiniteExact.cutRes_add_clock live none s entry none k cut (by simp)
    have bodyOk : result ≠ some .timeOut := by
      rintro rfl
      exact notTimeout rfl
    have rule := LoopWork.callRet (s := { s with clock := s.clock + k })
      (by rw [LoopSemStateFiniteExact.getVars_upd_clock]; exact args) find nodup cut'
      (ih bodyOk) plain
    rw [loopRetExit_add_clock] at rule
    exact rule
  | @callRetCont s names live target arguments exceptionName handlerProgram continuation liveOut
      values env prog entry returned post wb output wc args find nodup cut body lengths cont
      ihBody ihCont =>
    have cut' := LoopSemStateFiniteExact.cutRes_add_clock live none s entry none k cut (by simp)
    have contOk : output.1 ≠ some .timeOut := by
      intro h
      apply notTimeout
      obtain ⟨r, st⟩ := output
      simp only at h
      subst h
      simp [LoopSemStateFiniteExact.cutRes]
    have exit := LoopSemStateFiniteExact.cutRes_add_clock liveOut output.1 output.2
      (LoopSemStateFiniteExact.cutRes liveOut output).2
      (LoopSemStateFiniteExact.cutRes liveOut output).1 k rfl notTimeout
    have rule := LoopWork.callRetCont (s := { s with clock := s.clock + k })
      (exceptionName := exceptionName) (handlerProgram := handlerProgram) (liveOut := liveOut)
      (by rw [LoopSemStateFiniteExact.getVars_upd_clock]; exact args) find nodup cut'
      (ihBody (by simp)) lengths (ihCont contOk)
    rw [exit] at rule
    exact rule
  | @callHandle s names live target arguments exceptionName handlerProgram continuation liveOut
      values env prog entry exn post wb output wh args find nodup cut body handle ihBody
      ihHandle =>
    have cut' := LoopSemStateFiniteExact.cutRes_add_clock live none s entry none k cut (by simp)
    have handleOk : output.1 ≠ some .timeOut := by
      intro h
      apply notTimeout
      obtain ⟨r, st⟩ := output
      simp only at h
      subst h
      simp [LoopSemStateFiniteExact.cutRes]
    have exit := LoopSemStateFiniteExact.cutRes_add_clock liveOut output.1 output.2
      (LoopSemStateFiniteExact.cutRes liveOut output).2
      (LoopSemStateFiniteExact.cutRes liveOut output).1 k rfl notTimeout
    have rule := LoopWork.callHandle (s := { s with clock := s.clock + k })
      (continuation := continuation) (liveOut := liveOut)
      (by rw [LoopSemStateFiniteExact.getVars_upd_clock]; exact args) find nodup cut'
      (ihBody (by simp)) (ihHandle handleOk)
    rw [exit] at rule
    exact rule

#print axioms LoopWork.add_clock
end InitECandidate.Runtime.FineCost
