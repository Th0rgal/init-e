import InitECandidate.Runtime.CrepAffineWhile
namespace InitECandidate.Runtime
open Flapjack Classical

/-- The original call guard: return variables are distinct and a clock is available. -/
def crepCallGuard {width : Nat} [NeZero width] {F : Type}
    (caltyp : Option (List Nat × Option (BitVec width × CrepProgHOL width)))
    (s : CrepSemHOLState width F) : Prop :=
  ¬ (match caltyp with | none => False | some (rts, _) => ¬ rts.Nodup) ∧ s.clock ≠ 0

noncomputable def crepCallBodyBudget {width : Nat} [NeZero width] {F : Type} (limit : Nat)
    (caltyp : Option (List Nat × Option (BitVec width × CrepProgHOL width)))
    (fname : Flapjack.Basis.Pure.MlString.MlString) (es : List (CrepExpHOL width))
    (s : CrepSemHOLState width F) : Nat :=
  match es.mapM (evalCrepSemHOLExp s) with
  | none => 0
  | some args =>
    match lookupCodeFiniteHOL s.code fname args args.length with
    | none => 0
    | some (prog, nl) =>
      if crepCallGuard caltyp s then crepAffine limit prog {decClockCrepSemHOL s with locals := nl} else 0

noncomputable def crepCallHandlerBudget {width : Nat} [NeZero width] {F : Type} (limit : Nat)
    (caltyp : Option (List Nat × Option (BitVec width × CrepProgHOL width)))
    (fname : Flapjack.Basis.Pure.MlString.MlString) (es : List (CrepExpHOL width))
    (s : CrepSemHOLState width F) : Nat :=
  match es.mapM (evalCrepSemHOLExp s) with
  | none => 0
  | some args =>
    match lookupCodeFiniteHOL s.code fname args args.length with
    | none => 0
    | some (prog, nl) =>
      if crepCallGuard caltyp s then
        match caltyp with
        | some (_, some (eid', p)) =>
          match evalCrepSemHOLProgExact {decClockCrepSemHOL s with locals := nl} prog with
          | (some (.exception eid), st) =>
            if eid = eid' then crepAffine limit p {st with locals := s.locals} else 0
          | _ => 0
        | _ => 0
      else 0

set_option maxHeartbeats 4000000 in
/-- Handler budget selected by the actual callee result. -/
noncomputable def crepHandlerPick {width : Nat} [NeZero width] {F : Type} (limit : Nat)
    (eid' : BitVec width) (p : CrepProgHOL width) (s : CrepSemHOLState width F)
    (r : Option (CrepResultHOLExact width)) (m : CrepSemHOLState width F) : Nat :=
  match r with
  | some (.exception eid) => if eid = eid' then crepAffine limit p {m with locals := s.locals} else 0
  | _ => 0

theorem crep_call_affine {width : Nat} [NeZero width] {F : Type}
    (limit : Nat) (caltyp : Option (List Nat × Option (BitVec width × CrepProgHOL width)))
    (fname : Flapjack.Basis.Pure.MlString.MlString) (es : List (CrepExpHOL width))
    (s : CrepSemHOLState width F) (small : sizeOf (CrepProgHOL.call caltyp fname es) ≤ limit)
    (bounded : CrepCodeSize limit s) (ih : CrepAffineIH limit (.call caltyp fname es) s) :
    BoundedCrepPropertyAt (.call caltyp fname es) s (crepAffine limit (.call caltyp fname es) s) := by
  have hes := crepExpsFuel_le_size es
  have sizeSpec : sizeOf (CrepProgHOL.call caltyp fname es) = 1 + sizeOf caltyp + sizeOf fname + sizeOf es := by
    simp
  have lower (positive : s.clock ≠ 0) : (decClockCrepSemHOL s).clock < s.clock := by
    simp only [decClockCrepSemHOL]
    omega
  have run : BoundedCrepPropertyAt (.call caltyp fname es) s
      (crepExpsFuel es + crepCallBodyBudget limit caltyp fname es s +
        crepCallHandlerBudget limit caltyp fname es s + 3) := by
    intro result post target ctxt live hr hg hs hm hgl hc hl
    apply crep_call_bounded_step caltyp fname es s _ _ ?_ ?_ result post target ctxt live ⟨hr,hg,hs,hm,hgl,hc,hl⟩
    · intro args prog locals st eid rts handler h
      obtain ⟨hargs, hlc, nodup, positive, called, installed⟩ := h
      have clock := evalCrepSemHOLProgExact_clock_le {decClockCrepSemHOL s with locals := locals} prog
      rw [called] at clock
      have less : st.clock < s.clock := Nat.lt_of_le_of_lt clock (lower positive)
      have handlerSize : sizeOf handler < sizeOf (CrepProgHOL.call caltyp fname es) := by
        rw [installed]
        simp
        omega
      have guard : crepCallGuard caltyp s := ⟨nodup, positive⟩
      have budgetEq : crepCallHandlerBudget limit caltyp fname es s =
          crepAffine limit handler {st with locals := s.locals} := by
        unfold crepCallHandlerBudget
        rw [hargs]
        simp only [hlc, if_pos guard]
        subst installed
        simp only [called, if_true]
      rw [budgetEq]
      apply ih handler {st with locals := s.locals} (workRank_clock _ _ _ _ _ less (by omega)) (by omega)
      have stateBounded := bounded.decClock.setLocals locals
      have postBounded := stateBounded.evaluated prog
      have stBounded : CrepCodeSize limit st := postBounded.of_code_eq (by rw [called])
      exact stBounded.setLocals _
    · intro args prog locals h
      obtain ⟨hargs, hlc, nodup, positive⟩ := h
      have bodySize := bounded.lookup fname args prog locals hlc
      have guard : crepCallGuard caltyp s := ⟨nodup, positive⟩
      have budgetEq : crepCallBodyBudget limit caltyp fname es s =
          crepAffine limit prog {decClockCrepSemHOL s with locals := locals} := by
        unfold crepCallBodyBudget
        rw [hargs]
        simp only [hlc, if_pos guard]
      rw [budgetEq]
      exact ih prog _ (workRank_clock _ _ _ _ _ (lower positive) bodySize) bodySize
        (bounded.decClock.setLocals locals)
  apply crep_bounded_mono run
  have limitEs : crepExpsFuel es ≤ limit := by omega
  have esPositive : 1 ≤ sizeOf es := by cases es <;> simp <;> omega
  unfold crepAffine
  rw [evalCrepSemHOLProgExact_call]
  cases hargs : es.mapM (evalCrepSemHOLExp s) with
  | none => simp [crepCallBodyBudget, crepCallHandlerBudget, hargs]; omega
  | some args =>
    cases hcode : s.code.lookup fname with
    | none => simp [crepCallBodyBudget, crepCallHandlerBudget, hargs, lookupCodeFiniteHOL, hcode]; omega
    | some entry =>
      obtain ⟨params, body⟩ := entry
      by_cases ok : params.length = args.length ∧ params.Nodup
      · have hlc : lookupCodeFiniteHOL s.code fname args args.length =
            some (body, HolFiniteMapExact.empty.updateList (params.zip args)) := by
          unfold lookupCodeFiniteHOL; rw [hcode]; simp [ok]
        have bodySize := bounded.lookup fname args body _ hlc
        by_cases guard : crepCallGuard caltyp s
        · have positive : s.clock ≠ 0 := guard.2
          have hstate : decClockCrepSemHOL {s with locals := HolFiniteMapExact.empty.updateList (params.zip args)} =
              {decClockCrepSemHOL s with locals := HolFiniteMapExact.empty.updateList (params.zip args)} := rfl
          cases bodyRun : evalCrepSemHOLProgExact
              {decClockCrepSemHOL s with locals := HolFiniteMapExact.empty.updateList (params.zip args)} body with
          | mk r m =>
            have bodyClock : m.clock ≤ s.clock - 1 := by
              have h := evalCrepSemHOLProgExact_clock_le
                {decClockCrepSemHOL s with locals := HolFiniteMapExact.empty.updateList (params.zip args)} body
              rw [bodyRun] at h; exact h
            have bodyEq : crepCallBodyBudget limit caltyp fname es s =
                (5 * limit + 5) * (s.clock - 1 - m.clock) + 2 * sizeOf body := by
              unfold crepCallBodyBudget; rw [hargs]; simp only [hlc, if_pos guard]
              unfold crepAffine; rw [bodyRun]; rfl
            rw [bodyEq]
            have positive' : 1 ≤ s.clock := by omega
            have ending := affine_tick_end (5 * limit + 5) s.clock m.clock bodyClock positive'
            simp only [ok, decide_true, Bool.and_self, if_true, dif_neg positive]
            have sizeBody : 2 * sizeOf body + crepExpsFuel es + 3 ≤ 5 * limit + 5 := by omega
            cases caltyp with
            | none =>
              have hb0 : crepCallHandlerBudget limit none fname es s = 0 := by
                unfold crepCallHandlerBudget; rw [hargs]; simp only [hlc, if_pos guard]
              rw [hb0]
              simp only
              split
              all_goals
                have heq' := ‹fixClockCrepSemHOL _ (evalCrepSemHOLProgExact _ body) = _›
                rw [fixClockCrepSemHOL_evalCrepSemHOLProgExact, hstate, bodyRun] at heq'
                simp only [Prod.mk.injEq] at heq'
                obtain ⟨-, rfl⟩ := heq'
                simp only [CrepSemHOLState.emptyLocals]
                omega
            | some info =>
              obtain ⟨rts, handler⟩ := info
              have nodup : rts.Nodup := by
                have g := guard.1
                simp only [not_not] at g
                exact g
              simp only [if_pos nodup]
              cases handler with
              | none =>
                have hb0 : crepCallHandlerBudget limit (some (rts, none)) fname es s = 0 := by
                  unfold crepCallHandlerBudget; rw [hargs]; simp only [hlc, if_pos guard]
                rw [hb0]
                split
                all_goals
                  have heq' := ‹fixClockCrepSemHOL _ (evalCrepSemHOLProgExact _ body) = _›
                  rw [fixClockCrepSemHOL_evalCrepSemHOLProgExact, hstate, bodyRun] at heq'
                  simp only [Prod.mk.injEq] at heq'
                  obtain ⟨-, rfl⟩ := heq'
                  try simp only
                  repeat' split
                  all_goals (try simp only [CrepSemHOLState.emptyLocals])
                  all_goals (try dsimp only)
                  all_goals omega
              | some hinfo =>
                obtain ⟨eid', p⟩ := hinfo
                have pSize : sizeOf p < sizeOf (CrepProgHOL.call (some (rts, some (eid', p))) fname es) := by
                  simp; omega
                have hbEq : crepCallHandlerBudget limit (some (rts, some (eid', p))) fname es s =
                    crepHandlerPick limit eid' p s r m := by
                  unfold crepCallHandlerBudget; rw [hargs]; simp only [hlc, if_pos guard]; rw [bodyRun]
                  unfold crepHandlerPick
                  cases r with
                  | none => rfl
                  | some v => cases v <;> rfl
                have domains := evalCrepSemHOLProgExact_domains_of_eq bodyRun
                have stamp : crepStampExactDomains s {m with locals := s.locals} = {m with locals := s.locals} := by
                  simp only [crepStampExactDomains]
                  rw [domains.1, domains.2]
                  rfl
                split
                all_goals
                  have heq' := ‹fixClockCrepSemHOL _ (evalCrepSemHOLProgExact _ body) = _›
                  rw [fixClockCrepSemHOL_evalCrepSemHOLProgExact, hstate, bodyRun] at heq'
                  simp only [Prod.mk.injEq] at heq'
                  obtain ⟨rfl, rfl⟩ := heq'
                  rw [hbEq]
                  simp only [crepHandlerPick]
                  repeat' split
                  all_goals (try simp only [CrepSemHOLState.emptyLocals])
                  all_goals (try dsimp only)
                  all_goals first
                    | omega
                    | (try rw [stamp]
                       unfold crepAffine
                       have handlerClock := evalCrepSemHOLProgExact_clock_le {m with locals := s.locals} p
                       have ticking := affine_tick_split (5 * limit + 5) s.clock m.clock _ bodyClock handlerClock positive'
                       have hl : ({m with locals := s.locals} : CrepSemHOLState width F).clock = m.clock := rfl
                       simp only at *
                       omega)
                    | (exfalso
                       exact ‹∀ (eid : BitVec width), _ = CrepResultHOLExact.exception eid → False› _
                         (Option.some.inj ‹some _ = some (CrepResultHOLExact.exception _)›))
        · have zeroBudgets : crepCallBodyBudget limit caltyp fname es s = 0 ∧
              crepCallHandlerBudget limit caltyp fname es s = 0 := by
            constructor
            · unfold crepCallBodyBudget; rw [hargs]; simp only [hlc, if_neg guard]
            · unfold crepCallHandlerBudget; rw [hargs]; simp only [hlc, if_neg guard]
          rw [zeroBudgets.1, zeroBudgets.2]
          omega
      · have hlc : lookupCodeFiniteHOL s.code fname args args.length = none := by
          unfold lookupCodeFiniteHOL; rw [hcode]; simp only [if_neg ok]
        have zeroBudgets : crepCallBodyBudget limit caltyp fname es s = 0 ∧
            crepCallHandlerBudget limit caltyp fname es s = 0 := by
          constructor
          · unfold crepCallBodyBudget; rw [hargs]; simp only [hlc]
          · unfold crepCallHandlerBudget; rw [hargs]; simp only [hlc]
        rw [zeroBudgets.1, zeroBudgets.2]
        omega

#print axioms crep_call_affine
end InitECandidate.Runtime
