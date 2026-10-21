import InitECandidate.Runtime.SourceCostLoopWork
namespace InitECandidate.Runtime.FineCost
open Flapjack Flapjack.LoopSemStateFiniteExact

variable {L : LeafPrice}

/-! Executed Loop work with a parametric leaf price. Every non-leaf price is
the `LoopWork` constant; a `LeafPrice` charges leaves only on `LoopWork`'s leaf
kinds, and `skip` is free. `LoopWork` is `LoopWorkG defaultLeaf`. -/

/-- A Loop leaf price for the optimisation passes. -/
structure LeafPrice where
  lf : HolLoopProg 64 → Option Nat
  dom : ∀ p c, lf p = some c → (loopWorkLeafCost p).isSome = true
  skip : lf .skip = some 0
  ffiLive : ∀ f a b c d (l l' : NumSet), lf (.ffi f a b c d l) = lf (.ffi f a b c d l')

/-- The `LoopWork` leaf price. -/
def defaultLeaf : LeafPrice where
  lf := loopWorkLeafCost
  dom := fun p c h => by simp [h]
  skip := rfl
  ffiLive := fun _ _ _ _ _ _ _ => rfl

/-- Executed Loop work, indexed by the exact evaluator output. Every executed
statement pays its local cost; recursive rules expose only actual successors:
the selected branch, each loop iteration and the actual callee, continuation
or handler. -/
inductive LoopWorkG (L : LeafPrice) {F : Type} : LoopSemStateFiniteExact 64 F → HolLoopProg 64 →
    (Option (LoopResultExact 64) × LoopSemStateFiniteExact 64 F) → Nat → Prop where
  | atom {s p output cost} (leaf : L.lf p = some cost)
      (run : evaluate p s = output) : LoopWorkG L s p output cost
  | mark {s p output w} (inner : LoopWorkG L s p output w) : LoopWorkG L s (.mark p) output w
  | seqNext {s first second middle output a b}
      (one : LoopWorkG L s first (none, middle) a) (two : LoopWorkG L middle second output b) :
      LoopWorkG L s (.seq first second) output (a + b)
  | seqStop {s first second result post a} (one : LoopWorkG L s first (some result, post) a) :
      LoopWorkG L s (.seq first second) (some result, post) a
  | iteBranch {s operator register right yes no live x y output w}
      (lhs : sptLookup register s.locals = some (.word x))
      (rhs : LoopSemStateFiniteExact.getVarImm right s = some (.word y))
      (branch : LoopWorkG L s (if Compiler.Encoders.Asm.wordCmpHOL operator x y then yes else no)
        output w) :
      LoopWorkG L s (.ite operator register right yes no live) (LoopSemStateFiniteExact.cutRes live output) (37 + w)
  | iteInvalid {s operator register right yes no live}
      (invalid : ¬ ∃ x y, sptLookup register s.locals = some (.word x) ∧
        LoopSemStateFiniteExact.getVarImm right s = some (.word y)) :
      LoopWorkG L s (.ite operator register right yes no live) (some .error, s) 1
  | loopNext {s liveIn body liveOut entry result middle output wb wr}
      (cut : LoopSemStateFiniteExact.cutRes liveIn (none, s) = (none, entry))
      (one : LoopWorkG L entry body (result, middle) wb)
      (again : result = none ∨ result = some (.continue 0))
      (rest : LoopWorkG L middle (.loop liveIn body liveOut) output wr) :
      LoopWorkG L s (.loop liveIn body liveOut) output (16 + wb + wr)
  | loopBreak {s liveIn body liveOut entry middle wb}
      (cut : LoopSemStateFiniteExact.cutRes liveIn (none, s) = (none, entry))
      (one : LoopWorkG L entry body (some (.break 0), middle) wb) :
      LoopWorkG L s (.loop liveIn body liveOut) (LoopSemStateFiniteExact.cutRes liveOut (none, middle)) (16 + wb)
  | loopExit {s liveIn body liveOut entry result middle wb}
      (cut : LoopSemStateFiniteExact.cutRes liveIn (none, s) = (none, entry))
      (one : LoopWorkG L entry body (result, middle) wb)
      (stop : result ≠ none ∧ result ≠ some (.continue 0) ∧ result ≠ some (.break 0)) :
      LoopWorkG L s (.loop liveIn body liveOut) (LoopSemStateFiniteExact.exitLoop result, middle) (16 + wb)
  | loopCut {s liveIn body liveOut result cut}
      (stopped : LoopSemStateFiniteExact.cutRes liveIn (none, s) = (some result, cut)) :
      LoopWorkG L s (.loop liveIn body liveOut) (some result, cut) 16
  | callShort {s returns target arguments handler output}
      (short : loopCallShort s returns target arguments handler)
      (run : evaluate (.call returns target arguments handler) s = output) :
      LoopWorkG L s (.call returns target arguments handler) output (189 + 39 * arguments.length)
  | callTail {s target arguments handler values env prog result post wb}
      (args : LoopSemStateFiniteExact.getVars arguments s = some values)
      (find : LoopSemStateFiniteExact.findCode target values s.code = some (env, prog))
      (noHandler : handler.isSome = false) (clock : s.clock ≠ 0)
      (body : LoopWorkG L { LoopSemStateFiniteExact.decClock s with locals := env } prog (result, post) wb) :
      LoopWorkG L s (.call none target arguments handler) (loopTailExit result post)
        (189 + 39 * arguments.length + wb)
  | callRet {s names live target arguments handler values env prog entry result post wb}
      (args : LoopSemStateFiniteExact.getVars arguments s = some values)
      (find : LoopSemStateFiniteExact.findCode target values s.code = some (env, prog))
      (nodup : names.Nodup) (cut : LoopSemStateFiniteExact.cutRes live (none, s) = (none, entry))
      (body : LoopWorkG L { entry with locals := env } prog (result, post) wb)
      (plain : loopRetPlain result names handler) :
      LoopWorkG L s (.call (some (names, live)) target arguments handler)
        (loopRetExit result post entry names) (189 + 39 * arguments.length + wb + 49 * loopRetWords result)
  | callRetCont {s names live target arguments exceptionName handlerProgram continuation
      liveOut values env prog entry returned post wb output wc}
      (args : LoopSemStateFiniteExact.getVars arguments s = some values)
      (find : LoopSemStateFiniteExact.findCode target values s.code = some (env, prog))
      (nodup : names.Nodup) (cut : LoopSemStateFiniteExact.cutRes live (none, s) = (none, entry))
      (body : LoopWorkG L { entry with locals := env } prog (some (.result returned), post) wb)
      (lengths : returned.length = names.length)
      (cont : LoopWorkG L (LoopSemStateFiniteExact.setVars names returned { post with locals := entry.locals })
        continuation output wc) :
      LoopWorkG L s (.call (some (names, live)) target arguments
          (some (exceptionName, handlerProgram, continuation, liveOut)))
        (LoopSemStateFiniteExact.cutRes liveOut output) (196 + 39 * arguments.length + wb + 49 * returned.length + wc)
  | callHandle {s names live target arguments exceptionName handlerProgram continuation
      liveOut values env prog entry exn post wb output wh}
      (args : LoopSemStateFiniteExact.getVars arguments s = some values)
      (find : LoopSemStateFiniteExact.findCode target values s.code = some (env, prog))
      (nodup : names.Nodup) (cut : LoopSemStateFiniteExact.cutRes live (none, s) = (none, entry))
      (body : LoopWorkG L { entry with locals := env } prog (some (.exception exn), post) wb)
      (handle : LoopWorkG L (LoopSemStateFiniteExact.setVar exceptionName exn { post with locals := entry.locals })
        handlerProgram output wh) :
      LoopWorkG L s (.call (some (names, live)) target arguments
          (some (exceptionName, handlerProgram, continuation, liveOut)))
        (LoopSemStateFiniteExact.cutRes liveOut output) (196 + 39 * arguments.length + wb + wh)

theorem LoopWorkG.sound {F : Type} {s : LoopSemStateFiniteExact 64 F} {p : HolLoopProg 64}
    {output} {w : Nat} (work : LoopWorkG L s p output w) : evaluate p s = output := by
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

#print axioms LoopWorkG.sound

/-- Raising the clock does not change the work of a run that does not time
out: every sub-run on the executed path is then also non-timeout. -/
theorem LoopWorkG.add_clock {F : Type} {s : LoopSemStateFiniteExact 64 F} {p : HolLoopProg 64}
    {output : Option (LoopResultExact 64) × LoopSemStateFiniteExact 64 F} {w : Nat}
    (work : LoopWorkG L s p output w) (k : Nat) (notTimeout : output.1 ≠ some .timeOut) :
    LoopWorkG L { s with clock := s.clock + k } p
      (output.1, { output.2 with clock := output.2.clock + k }) w := by
  induction work with
  | @atom s p output cost leaf run =>
    refine LoopWorkG.atom leaf ?_
    exact evaluate_add_clock_eq p s output.1 output.2 k run notTimeout
  | mark inner ih => exact LoopWorkG.mark (ih notTimeout)
  | seqNext one two ihOne ihTwo =>
    exact LoopWorkG.seqNext (ihOne (by simp)) (ihTwo notTimeout)
  | seqStop one ih => exact LoopWorkG.seqStop (ih notTimeout)
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
    have rule := LoopWorkG.iteBranch (s := { s with clock := s.clock + k }) (live := live) lhs
      (by rw [LoopSemStateFiniteExact.getVarImm_upd_clock]; exact rhs) child
    rw [cut] at rule
    exact rule
  | @iteInvalid s operator register right yes no live invalid =>
    refine LoopWorkG.iteInvalid ?_
    rw [LoopSemStateFiniteExact.getVarImm_upd_clock]
    exact invalid
  | @loopNext s liveIn body liveOut entry result middle output wb wr cut one again rest ihOne
      ihRest =>
    have cut' := LoopSemStateFiniteExact.cutRes_add_clock liveIn none s entry none k cut (by simp)
    have bodyOk : result ≠ some .timeOut := by rcases again with rfl | rfl <;> simp
    exact LoopWorkG.loopNext cut' (ihOne bodyOk) again (ihRest notTimeout)
  | @loopBreak s liveIn body liveOut entry middle wb cut one ihOne =>
    have cut' := LoopSemStateFiniteExact.cutRes_add_clock liveIn none s entry none k cut (by simp)
    have exit := LoopSemStateFiniteExact.cutRes_add_clock liveOut none middle
      (LoopSemStateFiniteExact.cutRes liveOut (none, middle)).2
      (LoopSemStateFiniteExact.cutRes liveOut (none, middle)).1 k rfl notTimeout
    have rule := LoopWorkG.loopBreak (liveOut := liveOut) cut' (ihOne (by simp))
    simp only [] at rule
    rw [exit] at rule
    exact rule
  | @loopExit s liveIn body liveOut entry result middle wb cut one stop ihOne =>
    have cut' := LoopSemStateFiniteExact.cutRes_add_clock liveIn none s entry none k cut (by simp)
    have bodyOk : result ≠ some .timeOut := by
      rintro rfl
      exact notTimeout rfl
    exact LoopWorkG.loopExit cut' (ihOne bodyOk) stop
  | @loopCut s liveIn body liveOut result cut stopped =>
    exact LoopWorkG.loopCut
      (LoopSemStateFiniteExact.cutRes_add_clock liveIn none s cut (some result) k stopped notTimeout)
  | @callShort s returns target arguments handler output short run =>
    have run' := evaluate_add_clock_eq _ s output.1 output.2 k run notTimeout
    refine LoopWorkG.callShort ?_ run'
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
    have rule := LoopWorkG.callTail (s := { s with clock := s.clock + k })
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
    have rule := LoopWorkG.callRet (s := { s with clock := s.clock + k })
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
    have rule := LoopWorkG.callRetCont (s := { s with clock := s.clock + k })
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
    have rule := LoopWorkG.callHandle (s := { s with clock := s.clock + k })
      (continuation := continuation) (liveOut := liveOut)
      (by rw [LoopSemStateFiniteExact.getVars_upd_clock]; exact args) find nodup cut'
      (ihBody (by simp)) (ihHandle handleOk)
    rw [exit] at rule
    exact rule

#print axioms LoopWorkG.add_clock
theorem LoopWork.toG {F : Type} {s : LoopSemStateFiniteExact 64 F} {p : HolLoopProg 64} {output} {w : Nat}
    (work : LoopWork s p output w) : LoopWorkG defaultLeaf s p output w := by
  induction work with
  | atom leaf run => exact .atom leaf run
  | mark _ ih => exact .mark ih
  | seqNext _ _ ih1 ih2 => exact .seqNext ih1 ih2
  | seqStop _ ih => exact .seqStop ih
  | iteBranch lhs rhs _ ih => exact .iteBranch lhs rhs ih
  | iteInvalid invalid => exact .iteInvalid invalid
  | loopNext cut _ again _ ih1 ih2 => exact .loopNext cut ih1 again ih2
  | loopBreak cut _ ih => exact .loopBreak cut ih
  | loopExit cut _ stop ih => exact .loopExit cut ih stop
  | loopCut stopped => exact .loopCut stopped
  | callShort short run => exact .callShort short run
  | callTail args find noHandler clock _ ih => exact .callTail args find noHandler clock ih
  | callRet args find nodup cut _ plain ih => exact .callRet args find nodup cut ih plain
  | callRetCont args find nodup cut _ lengths _ ih1 ih2 => exact .callRetCont args find nodup cut ih1 lengths ih2
  | callHandle args find nodup cut _ _ ih1 ih2 => exact .callHandle args find nodup cut ih1 ih2

theorem LoopWorkG.toW {F : Type} {s : LoopSemStateFiniteExact 64 F} {p : HolLoopProg 64} {output} {w : Nat}
    (work : LoopWorkG defaultLeaf s p output w) : LoopWork s p output w := by
  induction work with
  | atom leaf run => exact .atom leaf run
  | mark _ ih => exact .mark ih
  | seqNext _ _ ih1 ih2 => exact .seqNext ih1 ih2
  | seqStop _ ih => exact .seqStop ih
  | iteBranch lhs rhs _ ih => exact .iteBranch lhs rhs ih
  | iteInvalid invalid => exact .iteInvalid invalid
  | loopNext cut _ again _ ih1 ih2 => exact .loopNext cut ih1 again ih2
  | loopBreak cut _ ih => exact .loopBreak cut ih
  | loopExit cut _ stop ih => exact .loopExit cut ih stop
  | loopCut stopped => exact .loopCut stopped
  | callShort short run => exact .callShort short run
  | callTail args find noHandler clock _ ih => exact .callTail args find noHandler clock ih
  | callRet args find nodup cut _ plain ih => exact .callRet args find nodup cut ih plain
  | callRetCont args find nodup cut _ lengths _ ih1 ih2 => exact .callRetCont args find nodup cut ih1 lengths ih2
  | callHandle args find nodup cut _ _ ih1 ih2 => exact .callHandle args find nodup cut ih1 ih2

#print axioms LoopWork.toG
#print axioms LoopWorkG.toW
end InitECandidate.Runtime.FineCost
