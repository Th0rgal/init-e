import InitECandidate.Runtime.SourceCostLoopCallBase
namespace InitECandidate.Runtime.FineCost
open Flapjack Flapjack.Pancake.CrepToLoop.Proofs.NCompileCorrect

theorem loopCall_resultToLoop_ok {r : CrepResultHOLExact 64} (hre : r ≠ .error)
    (hrb : ∀ n, r ≠ .break n) (hrc : ∀ n, r ≠ .continue n) :
    resultToLoop (some r) ≠ some .error ∧ (∀ n, resultToLoop (some r) ≠ some (.break n)) ∧
      (∀ n, resultToLoop (some r) ≠ some (.continue n)) := by
  cases r <;> simp_all [resultToLoop]

theorem loopCall_some_ok {r : CrepResultHOLExact 64} {x : LoopSemStateFiniteExact.LoopResultExact 64}
    (hx : resultToLoop (some r) = some x) (hre : r ≠ .error)
    (hrb : ∀ n, r ≠ .break n) (hrc : ∀ n, r ≠ .continue n) :
    x ≠ .error ∧ (∀ n, x ≠ .break n) ∧ (∀ n, x ≠ .continue n) := by
  cases r <;> simp only [resultToLoop, Option.some.injEq] at hx <;> subst hx <;> simp_all

/-- Crep→Loop executed-work transfer for `call`, conditional on the named
temporary `LoopOptimiseWork` contract for the per-function `optimiseHOL` pass
installed by `compile_prog`. The relation reasoning is the pinned
`crepToLoop_ncompile_correct_call` proof; each executed site adds its
`LoopWork` rule: argument code and moves, the call, the actual callee body,
the return-slot copy or the matched handler dispatch. -/
theorem call_loop_paid {F : Type} (opt : LoopOptimiseWork)
    (caltyp : Option (List Nat × Option (BitVec 64 × CrepProgHOL 64)))
    (fname : Flapjack.Basis.Pure.MlString.MlString) (argexps : List (CrepExpHOL 64))
    (v1 : CrepSemHOLState 64 F) (t : LoopSemStateFiniteExact 64 F)
    (ctxt : CrepToLoopContextExact) (l : NumSet) (w : Nat)
    (ok : (evalCrepSemHOLProgExact v1 (.call caltyp fname argexps)).1 ≠ some .error)
    (rel : CrepLoopRel ctxt l v1 t)
    (shortW : v1.clock = 0 → 1 + crepListWork argexps ≤ w)
    (ihb : ∀ (args : List (HolWordLab 64)) (prog : CrepProgHOL 64)
        (newlocals : HolFiniteMapExact Nat (HolWordLab 64)),
      argexps.mapM (evalCrepSemHOLExp v1) = some args →
      lookupCodeFiniteHOL v1.code fname args args.length = some (prog, newlocals) →
      ¬ (match caltyp with | none => False | some (rts, _) => ¬ rts.Nodup) →
      v1.clock ≠ 0 →
      ∃ wb,
        (∀ (u' : LoopSemStateFiniteExact 64 F) (c' : CrepToLoopContextExact) (l' : NumSet),
          (evalCrepSemHOLProgExact { decClockCrepSemHOL v1 with locals := newlocals } prog).1 ≠
            some .error →
          CrepLoopRel c' l' { decClockCrepSemHOL v1 with locals := newlocals } u' →
          LoopPaid c' l' { decClockCrepSemHOL v1 with locals := newlocals } u' prog wb) ∧
        (∀ r post, evalCrepSemHOLProgExact { decClockCrepSemHOL v1 with locals := newlocals } prog =
            (r, post) →
          (∀ eid rts hp, r = some (.exception eid) → caltyp ≠ some (rts, some (eid, hp))) →
          1 + crepListWork argexps + args.length + wb + crepCallPayloadWords r ≤ w) ∧
        (∀ (st : CrepSemHOLState 64 F) (eid : BitVec 64) (rts : List Nat) (hp : CrepProgHOL 64),
          evalCrepSemHOLProgExact { decClockCrepSemHOL v1 with locals := newlocals } prog =
            (some (.exception eid), st) →
          caltyp = some (rts, some (eid, hp)) →
          ∃ wh,
            (∀ u' : LoopSemStateFiniteExact 64 F,
              (evalCrepSemHOLProgExact { st with locals := v1.locals } hp).1 ≠ some .error →
              CrepLoopRel ctxt l { st with locals := v1.locals } u' →
              LoopPaid ctxt l { st with locals := v1.locals } u' hp wh) ∧
            1 + crepListWork argexps + args.length + wb + wh ≤ w)) :
    LoopPaid ctxt l v1 t (.call caltyp fname argexps) w := by
  classical
  rcases hEvalAll : evalCrepSemHOLProgExact v1 (.call caltyp fname argexps) with ⟨res, s1⟩
  have hne : res ≠ some .error := by rw [hEvalAll] at ok; exact ok
  have hs := rel.state
  have hm := rel.memory
  have hg := rel.globals
  have hc := rel.code
  have hl := rel.locals
  have he := hEvalAll
  suffices core : ∃ (ck : Nat) (res1 : Option (LoopSemStateFiniteExact.LoopResultExact 64))
      (t1 : LoopSemStateFiniteExact 64 F),
      LoopSemStateFiniteExact.evaluate (compileHOLExact ctxt l (.call caltyp fname argexps))
        { t with clock := t.clock + ck } = (res1, t1) ∧
      crepToLoopStateRelExact s1 t1 ∧
      crepToLoopMemRelHOLExact s1.memory t1.memory s1.memaddrs ∧
      crepToLoopGlobalsRelHOLExact s1.globals t1.globals ∧
      crepToLoopCodeRelExact ctxt s1.code t1.code ∧
      res1 = resultToLoop res ∧
      localsResultRel ctxt l res s1 t1 ∧
      ∃ wl, LoopWork { t with clock := t.clock + ck }
        (compileHOLExact ctxt l (.call caltyp fname argexps)) (res1, t1) wl ∧ wl ≤ 7 * w by
    obtain ⟨ck, res1, t1, run, s, m, g, c, r, lr, wl, work, bound⟩ := core
    refine ⟨ck, wl, ?_, bound, ?_⟩
    · rw [run]; exact work
    · rw [hEvalAll, run]; exact ⟨s, m, g, c, r, lr⟩
  rw [evalCrepSemHOLProgExact_eq_evaluate_def] at he
  simp only at he
  cases hargs : argexps.mapM (evalCrepSemHOLExp v1) with
  | none =>
    simp only [hargs, Prod.mk.injEq] at he
    exact absurd he.1.symm hne
  | some args =>
  simp only [hargs] at he
  cases hlc : lookupCodeFiniteHOL v1.code fname args args.length with
  | none =>
    simp only [hlc, Prod.mk.injEq] at he
    exact absurd he.1.symm hne
  | some pn =>
  obtain ⟨prog, newlocals⟩ := pn
  simp only [hlc] at he
  -- the callee, from `lookup_code` and `code_rel`
  obtain ⟨ns, hcode, hnslen, hnsnd, rfl⟩ : ∃ ns, v1.code.lookup fname = some (ns, prog) ∧
      ns.length = args.length ∧ ns.Nodup ∧
      newlocals = HolFiniteMapExact.empty.updateList (ns.zip args) := by
    unfold lookupCodeFiniteHOL at hlc
    cases hcf : v1.code.lookup fname with
    | none => simp [hcf] at hlc
    | some q =>
      obtain ⟨ns, body⟩ := q
      simp only [hcf] at hlc
      by_cases hok : ns.length = args.length ∧ ns.Nodup
      · rw [if_pos hok] at hlc
        simp only [Option.some.injEq, Prod.mk.injEq] at hlc
        obtain ⟨rfl, rfl⟩ := hlc
        exact ⟨ns, rfl, hok.1, hok.2, rfl⟩
      · rw [if_neg hok] at hlc; cases hlc
  -- compiled arguments
  rcases hC : compileExpsHOLExact ctxt (ctxt.vmax + 1) l argexps with ⟨p, les, ntmp, nl⟩
  obtain ⟨ck, st, h1, hles, h1s, h1m, h1g, h1c, h1l⟩ :=
    crepToLoop_comp_exps_preserves_eval argexps v1 args t ctxt (ctxt.vmax + 1) l p les ntmp nl
      ⟨hargs, hs, hm, hg, hc, hl, hC, Nat.lt_succ_self _⟩
  obtain ⟨hokA, htA, hlA, hlesLen⟩ := compile_exp_out_rel_cases.2 ctxt (ctxt.vmax + 1) l argexps p
    les ntmp nl hC
  have hlen : les.length = args.length := by
    have := congrArg List.length ((optMmapEqSome les _ _).mp hles)
    simpa using this
  obtain ⟨hdf, hcodeF⟩ := h1c
  obtain ⟨loc, len, hfl, hnlen, hcl⟩ := hcodeF fname ns prog hcode
  -- the argument temporaries (as in the Return case)
  let temps := genTemps ntmp les.length
  have htlen : temps.length = les.length := by simp [temps, genTemps]
  have htnodup : temps.Nodup := by
    simp only [temps, genTemps]
    rw [List.Nodup, List.pairwise_map]
    exact (List.nodup_range).imp (fun h => by omega)
  have hdisj : distinctListsHol temps (les.map holLoopLocalsTouched).flatten = true := by
    simp only [distinctListsHol, List.all_eq_true, decide_eq_true_eq]
    intro x hx hmem
    have hx' : ntmp ≤ x := by
      simp only [temps, genTemps, List.mem_map, List.mem_range] at hx
      obtain ⟨a, _, rfl⟩ := hx; omega
    have := (compile_exps_le_tmp_domain ctxt (ctxt.vmax + 1) l argexps p les ntmp nl x
      ⟨hl.2.1, hC, Nat.lt_succ_self _, fun k hk => by
        obtain ⟨w, hw⟩ := crepOptMmapEval_some_var_cexp_local_lookup v1 argexps args k ⟨hargs, hk⟩
        obtain ⟨m, hm1, hm2, _⟩ := hl.2.2.2 k w hw
        exact ⟨m, hm1, hm2⟩, hmem⟩).1
    omega
  let vals := args.map wlabWlocExact
  let sA : LoopSemStateFiniteExact 64 F :=
    { st with locals := LoopSemStateFiniteExact.sptAlistInsert temps vals st.locals }
  have hget : LoopSemStateFiniteExact.getVars temps sA = some vals :=
    LoopSemStateFiniteExact.get_vars_local_update_some_eq temps vals st htnodup
      (by simp [vals, htlen, hlen])
  have hlab : findLabExact ctxt fname = loc := by simp [findLabExact, hfl]
  have hlenA : len = args.length := hnlen ▸ hnslen
  let nctxt := ctxtFcExact ctxt.target ctxt.funcs ns (List.range len)
  have hfind : LoopSemStateFiniteExact.findCode (some loc) vals sA.code =
      some (sptFromAList ((List.range len).zip vals),
        ocompileHOLExact nctxt (listToNumSetHOLExact (List.range len)) prog) := by
    simp only [LoopSemStateFiniteExact.findCode, sA]
    rw [hcl]
    simp [vals, hlenA, nctxt]
  -- the compiled arguments and assigns, from any clock extension
  have hpre : ∀ k (rest : List (HolLoopProg 64)),
      LoopSemStateFiniteExact.evaluate
        (loopNestedSeqHOL (p ++ temps.zipWith HolLoopProg.assign les ++ rest))
        { t with clock := t.clock + (ck + k) } =
      LoopSemStateFiniteExact.evaluate (loopNestedSeqHOL rest)
        { sA with clock := sA.clock + k } := by
    intro k rest
    have h1k : LoopSemStateFiniteExact.evaluate (loopNestedSeqHOL p)
        { t with clock := t.clock + (ck + k) } = (none, { st with clock := st.clock + k }) := by
      have := LoopSemStateFiniteExact.evaluate_add_clock_eq _ _ _ _ k h1 (by simp)
      simpa [Nat.add_assoc] using this
    have hmapk : les.map (LoopSemStateFiniteExact.eval { st with clock := st.clock + k }) =
        vals.map some := by
      rw [← (optMmapEqSome les _ _).mp hles]
      congr 1; funext x; exact LoopSemStateFiniteExact.eval_upd_clock_eq _ _ _
    have hassign := LoopSemStateFiniteExact.loop_eval_nested_assign_distinct_eq les temps
      { st with clock := st.clock + k } vals ⟨hmapk, hdisj, htnodup, htlen⟩
    rw [List.append_assoc, LoopSemStateFiniteExact.evaluate_nested_seq_append_none p _ _ _ h1k,
      LoopSemStateFiniteExact.evaluate_nested_seq_append_none _ _ _ _ hassign]
  -- executed work of the argument code and argument moves
  obtain ⟨preCode, preSupported, preBound⟩ := crep_to_loop_list_work ctxt (ctxt.vmax + 1) l argexps
  rw [hC] at preSupported preBound
  try dsimp only at preSupported preBound
  obtain ⟨moveCost, moveSupported, moveBound⟩ := assign_codes_work temps les
  have preAllowance : loopExpressionCodesWork (p ++ temps.zipWith HolLoopProg.assign les) =
      some (preCode + moveCost) := by
    rw [loopExpressionCodesWork_append, preSupported, moveSupported]; rfl
  have argWork := crepListWork_ge_length argexps
  have argLen : args.length = argexps.length := (opt_mmap_length_eq _ _ _ hargs).symm
  have tempsLen : temps.length = args.length := by rw [htlen, hlen]
  have finish : ∀ (k : Nat) (stmt : HolLoopProg 64)
      (o : Option (LoopSemStateFiniteExact.LoopResultExact 64) × LoopSemStateFiniteExact 64 F)
      (wc : Nat) (R : Option (LoopSemStateFiniteExact.LoopResultExact 64))
      (T : LoopSemStateFiniteExact 64 F),
      LoopWork { sA with clock := sA.clock + k } stmt o wc →
      LoopSemStateFiniteExact.evaluate
        (loopNestedSeqHOL (p ++ temps.zipWith HolLoopProg.assign les ++ [stmt]))
        { t with clock := t.clock + (ck + k) } = (R, T) →
      ∃ wl, LoopWork { t with clock := t.clock + (ck + k) }
        (loopNestedSeqHOL (p ++ temps.zipWith HolLoopProg.assign les ++ [stmt])) (R, T) wl ∧
        wl ≤ preCode + moveCost + wc := by
    intro k stmt o wc R T stmtWork run
    have preRun : LoopSemStateFiniteExact.evaluate
        (loopNestedSeqHOL (p ++ temps.zipWith HolLoopProg.assign les))
        { t with clock := t.clock + (ck + k) } = (none, { sA with clock := sA.clock + k }) := by
      have := hpre k []
      simpa [loopNestedSeqHOL, LoopSemStateFiniteExact.evaluate] using this
    have tailWork : ∃ wt, LoopWork { sA with clock := sA.clock + k } (loopNestedSeqHOL [stmt]) o wt ∧
        wt ≤ wc := by
      rcases o with ⟨_ | r, post⟩
      · have skipWork : LoopWork post (loopNestedSeqHOL ([] : List (HolLoopProg 64))) (none, post) 0 :=
          LoopWork.atom (cost := 0) rfl (by rw [loopNestedSeqHOL, LoopSemStateFiniteExact.evaluate])
        exact ⟨wc + 0, LoopWork.seqNext stmtWork skipWork, by omega⟩
      · exact ⟨wc, LoopWork.seqStop stmtWork, Nat.le_refl _⟩
    obtain ⟨wt, tWork, tBound⟩ := tailWork
    obtain ⟨wl, work, bound⟩ := loopWork_codes_append _ [stmt] _ _ _ o wt preAllowance preRun tWork
    have sound := LoopWork.sound work
    rw [run] at sound
    rw [← sound] at work
    exact ⟨wl, work, by omega⟩
  -- the callee's initial state, context and locals
  obtain ⟨hSc, hCc, hLc⟩ := crepToLoopCallPreserveStateCodeLocalsRelExact ns (List.range len)
    args v1 st ctxt nl fname argexps prog loc hnsnd List.nodup_range (by simp [hnlen])
    (by simp [hlenA]) h1s h1m h1g ⟨hdf, hcodeF⟩ h1l hcode (by simpa using hfl)
    ((optMmapEqSome argexps _ _).mp hargs)
  cases caltyp with
  | none =>
    simp only [if_false] at he
    have hcomp : compileHOLExact ctxt l (.call none fname argexps) =
        loopNestedSeqHOL (p ++ temps.zipWith HolLoopProg.assign les ++
          [HolLoopProg.call none (some loc) temps none]) := by
      rw [compileHOLExact, hC]; simp only [hlab]; rfl
    rw [hcomp]
    have hgkT : ∀ k, LoopSemStateFiniteExact.getVars temps { sA with clock := sA.clock + k } =
        some vals := by
      intro k
      simp only [sA]
      rw [LoopSemStateFiniteExact.get_vars_local_clock_upd_eq]; exact hget
    by_cases hz : v1.clock = 0
    · simp only [hz, if_true, Prod.mk.injEq] at he
      obtain ⟨rfl, rfl⟩ := he
      have hst0 : st.clock = 0 := h1s.2.2.1 ▸ hz
      have hrunF : LoopSemStateFiniteExact.evaluate (loopNestedSeqHOL (p ++ temps.zipWith HolLoopProg.assign les ++ [HolLoopProg.call none (some loc) temps none]))
          { t with clock := t.clock + (ck + 0) } =
          (some .timeOut, { sA with clock := sA.clock + 0, locals := .ln }) := by
        have hcall0 : LoopSemStateFiniteExact.evaluate (HolLoopProg.call none (some loc) temps none)
            { sA with clock := sA.clock + 0 } =
            (some .timeOut, { sA with clock := sA.clock + 0, locals := .ln }) := by
          rw [LoopSemStateFiniteExact.evaluate]
          simp only [hgkT 0]
          rw [hfind]
          simp only [Option.isSome_none, Bool.false_eq_true, if_false]
          have hz0 : sA.clock = 0 := hst0
          simp [hz0]
        rw [hpre 0 _]
        simp only [loopNestedSeqHOL, LoopSemStateFiniteExact.evaluate_seq, hcall0]
      have callWork := LoopWork.callShort (s := { sA with clock := sA.clock + 0 })
        (returns := none) (target := some loc) (arguments := temps) (handler := none)
        (Or.inr ⟨vals, hgkT 0, Or.inr ⟨_, _, hfind, Or.inl ⟨rfl, Or.inr (by
          show st.clock + 0 = 0; omega)⟩⟩⟩) rfl
      obtain ⟨wl, wlWork, wlBound⟩ := finish 0 _ _ _ _ _ callWork hrunF
      refine ⟨ck + 0, some .timeOut, { sA with clock := sA.clock + 0, locals := .ln }, hrunF, h1s,
        h1m, h1g, ⟨hdf, hcodeF⟩, rfl, trivial, wl, wlWork, ?_⟩
      have := shortW hz
      omega
    · simp only [hz, if_false] at he
      have hstz : st.clock ≠ 0 := h1s.2.2.1 ▸ hz
      obtain ⟨wb, ihBody, bodyBound, handlerBound⟩ := ihb args prog _ hargs hlc (by simp) hz
      have hw : (wlabWlocExact : HolWordLab 64 → WordLocW 64) = wlabWlocHOL := by
        funext v; cases v; rfl
      let T0 : LoopSemStateFiniteExact 64 F :=
        { st with locals := sptFromAList ((List.range len).zip (args.map wlabWlocHOL)),
                  clock := st.clock - 1 }
      -- a callee run ending in any result other than NONE/Break/Continue/Error
      have key : ∀ (r : CrepResultHOLExact 64) (st' : CrepSemHOLState 64 F),
          evalCrepSemHOLProgExact
              { decClockCrepSemHOL v1 with
                  locals := HolFiniteMapExact.empty.updateList (ns.zip args) } prog =
            (some r, st') →
          r ≠ .error → (∀ n, r ≠ .break n) → (∀ n, r ≠ .continue n) →
          ∃ (ck' : Nat) (t1 : LoopSemStateFiniteExact 64 F),
            LoopSemStateFiniteExact.evaluate (HolLoopProg.call none (some loc) temps none)
                { sA with clock := sA.clock + ck' } = (resultToLoop (some r), t1) ∧
            crepToLoopStateRelExact st' t1 ∧
            crepToLoopMemRelHOLExact st'.memory t1.memory st'.memaddrs ∧
            crepToLoopGlobalsRelHOLExact st'.globals t1.globals ∧
            crepToLoopCodeRelExact ctxt st'.code t1.code ∧
            ∃ wc, LoopWork { sA with clock := sA.clock + ck' } (HolLoopProg.call none (some loc) temps none)
              (resultToLoop (some r), t1) wc ∧ wc ≤ 1 + temps.length + 7 * wb := by
        intro r st' hb hre hrb hrc
        obtain ⟨ck', wbody, bodyWork, bodyWorkBound, bodyRel⟩ := ihBody T0 nctxt
          (listToNumSetHOLExact (List.range len)) (by rw [hb]; simpa using hre)
          ⟨hSc, h1m, h1g, hCc, hLc⟩
        rw [hb] at bodyRel
        rcases h2 : LoopSemStateFiniteExact.evaluate
            (compileHOLExact nctxt (listToNumSetHOLExact (List.range len)) prog)
            { T0 with clock := T0.clock + ck' } with ⟨res1', t1⟩
        rw [h2] at bodyRel bodyWork
        obtain ⟨h2s, h2m, h2g, h2c, h2r, _⟩ := bodyRel
        try dsimp only at h2s h2m h2g h2c h2r
        subst h2r
        have okR := loopCall_resultToLoop_ok hre hrb hrc
        have hopt := optimise_correct _ _ _ _ ⟨h2, okR.1, okR.2.1, okR.2.2,
          by cases r <;> simp [resultToLoop]⟩
        have hrec : ({ LoopSemStateFiniteExact.decClock { sA with clock := sA.clock + ck' } with
            locals := sptFromAList ((List.range len).zip vals) } : LoopSemStateFiniteExact 64 F) =
            { T0 with clock := T0.clock + ck' } := by
          simp only [LoopSemStateFiniteExact.decClock, sA, T0, vals, hw]
          congr 1
          omega
        obtain ⟨x, hx⟩ : ∃ x, resultToLoop (some r) = some x := by cases r <;> exact ⟨_, rfl⟩
        rw [hx] at bodyWork
        obtain ⟨wopt, optWork, optBound⟩ := opt F _ _ x t1 wbody bodyWork
          (loopCall_some_ok hx hre hrb hrc).1 (loopCall_some_ok hx hre hrb hrc).2.1
          (loopCall_some_ok hx hre hrb hrc).2.2
        rw [← hrec] at optWork
        have callWork := LoopWork.callTail (s := { sA with clock := sA.clock + ck' })
          (handler := none) (hgkT ck') hfind rfl (by show st.clock + ck' ≠ 0; omega) optWork
        have exitEq : loopTailExit (some x) t1 = (resultToLoop (some r), t1) := by
          rw [hx]
          cases r with
          | «break» n => exact absurd rfl (hrb n)
          | «continue» n => exact absurd rfl (hrc n)
          | error => exact absurd rfl hre
          | _ => simp only [resultToLoop, Option.some.injEq] at hx; subst hx; rfl
        rw [exitEq] at callWork
        refine ⟨ck', t1, LoopWork.sound callWork, h2s, h2m, h2g, h2c, _, callWork, by omega⟩
      split at he
      · simp only [Prod.mk.injEq] at he; exact absurd he.1.symm hne
      · simp only [Prod.mk.injEq] at he; exact absurd he.1.symm hne
      · simp only [Prod.mk.injEq] at he; exact absurd he.1.symm hne
      · rename_i _ retvs st' heq
        simp only [Prod.mk.injEq] at he
        obtain ⟨rfl, rfl⟩ := he
        obtain ⟨ck', t1, h3, h3s, h3m, h3g, h3c, wc, callWork, callBound⟩ :=
          key (.return retvs) st' heq (by simp) (by simp) (by simp)
        have hrunF : LoopSemStateFiniteExact.evaluate (loopNestedSeqHOL (p ++ temps.zipWith HolLoopProg.assign les ++ [HolLoopProg.call none (some loc) temps none]))
            { t with clock := t.clock + (ck + ck') } = (resultToLoop (some (.return retvs)), t1) := by
          rw [hpre ck' _]
          simp only [loopNestedSeqHOL, LoopSemStateFiniteExact.evaluate_seq, h3]
          rfl
        obtain ⟨wl, wlWork, wlBound⟩ := finish ck' _ _ _ _ _ callWork hrunF
        have crepBound := bodyBound _ _ heq (by intro _ _ _ _ h; cases h)
        refine ⟨ck + ck', resultToLoop (some (.return retvs)), t1, hrunF, h3s, h3m, h3g, h3c, rfl, trivial,
          wl, wlWork, ?_⟩
        simp only [crepCallPayloadWords] at crepBound
        omega
      · rename_i _ eid st' heq
        simp only [Prod.mk.injEq] at he
        obtain ⟨rfl, rfl⟩ := he
        obtain ⟨ck', t1, h3, h3s, h3m, h3g, h3c, wc, callWork, callBound⟩ :=
          key (.exception eid) st' heq (by simp) (by simp) (by simp)
        have hrunF : LoopSemStateFiniteExact.evaluate (loopNestedSeqHOL (p ++ temps.zipWith HolLoopProg.assign les ++ [HolLoopProg.call none (some loc) temps none]))
            { t with clock := t.clock + (ck + ck') } = (resultToLoop (some (.exception eid)), t1) := by
          rw [hpre ck' _]
          simp only [loopNestedSeqHOL, LoopSemStateFiniteExact.evaluate_seq, h3]
          rfl
        obtain ⟨wl, wlWork, wlBound⟩ := finish ck' _ _ _ _ _ callWork hrunF
        have crepBound := bodyBound _ _ heq (by intro _ _ _ _ h; cases h)
        refine ⟨ck + ck', resultToLoop (some (.exception eid)), t1, hrunF, h3s, h3m, h3g, h3c, rfl, trivial,
          wl, wlWork, ?_⟩
        simp only [crepCallPayloadWords] at crepBound
        omega
      · rename_i _ r' st' hn hb hcn hr hx heq
        simp only [Prod.mk.injEq] at he
        obtain ⟨rfl, rfl⟩ := he
        rcases r' with _ | r
        · exact absurd rfl hn
        have hre : r ≠ .error := fun h => hne (by rw [h])
        obtain ⟨ck', t1, h3, h3s, h3m, h3g, h3c, wc, callWork, callBound⟩ :=
          key r st' heq hre (fun n h => hb n (by rw [h])) (fun n h => hcn n (by rw [h]))
        have hrunF : LoopSemStateFiniteExact.evaluate (loopNestedSeqHOL (p ++ temps.zipWith HolLoopProg.assign les ++ [HolLoopProg.call none (some loc) temps none]))
            { t with clock := t.clock + (ck + ck') } = (resultToLoop (some r), t1) := by
          rw [hpre ck' _]
          simp only [loopNestedSeqHOL, LoopSemStateFiniteExact.evaluate_seq, h3]
          cases r <;> rfl
        obtain ⟨wl, wlWork, wlBound⟩ := finish ck' _ _ _ _ _ callWork hrunF
        have crepBound := bodyBound _ _ heq (by intro _ _ _ _ h; cases h)
        refine ⟨ck + ck', resultToLoop (some r), t1, hrunF, h3s, h3m, h3g, h3c, rfl, ?_,
          wl, wlWork, ?_⟩
        · cases r <;> first | exact True.intro | exact (hb _ rfl).elim | exact (hcn _ rfl).elim | exact (hre rfl).elim
        · omega
  | some rh =>
    obtain ⟨rts, hdl⟩ := rh
    by_cases hnd : rts.Nodup
    · simp only [hnd, not_true_eq_false, if_false] at he
      let rn : List Nat := match rts.mapM ctxt.vars.lookup with
        | none => [ctxt.vmax + 2]
        | some names => names
      let hbody : HolLoopProg 64 := match hdl with
        | none => .raise (ctxt.vmax + 1)
        | some (exception, hp) =>
            .ite .notEqual (ctxt.vmax + 1) (.imm exception)
              (.raise (ctxt.vmax + 1)) (.seq .tick (compileHOLExact ctxt l hp)) l
      have hcomp : compileHOLExact ctxt l (.call (some (rts, hdl)) fname argexps) =
          loopNestedSeqHOL (p ++ temps.zipWith HolLoopProg.assign les ++
            [HolLoopProg.call (some (rn, l)) (some loc) temps
              (some (ctxt.vmax + 1, hbody, .skip, l))]) := by
        rw [compileHOLExact, hC]; simp only [hlab]; cases hdl <;> rfl
      rw [hcomp]
      have hrnnd : rn.Nodup := by
        have h := allDistinctCtxtLookupAllDistinctExact ctxt rts (ctxt.vmax + 1) hnd hl.1
        simp only [rtVars, FLOOKUP] at h
        simp only [rn]
        cases hm : rts.mapM ctxt.vars.lookup with
        | none => simp
        | some names =>
          have hm' : rts.mapM (fun v => ctxt.vars.lookup v) = some names := hm
          rw [hm'] at h; exact h
      have hsubA : LoopSemStateFiniteExact.sptSubsetLive l sA.locals := by
        intro k hk
        have hkst : sptMem k st.locals := h1l.2.2.1 k (hlA ▸ cut_sets_union_domain_subset _ l hokA k hk)
        show (sptLookup k (LoopSemStateFiniteExact.sptAlistInsert temps vals st.locals)).isSome
        rw [lookup_alist_insert_any]
        split
        · exact hkst
        · rfl
      have hgk : ∀ k, LoopSemStateFiniteExact.getVars temps { sA with clock := sA.clock + k } =
          some vals := by
        intro k
        simp only [sA]
        rw [LoopSemStateFiniteExact.get_vars_local_clock_upd_eq]; exact hget
      by_cases hz : v1.clock = 0
      · simp only [hz, if_true, Prod.mk.injEq] at he
        obtain ⟨rfl, rfl⟩ := he
        have hst0 : st.clock = 0 := h1s.2.2.1 ▸ hz
        have hc0 : LoopSemStateFiniteExact.cutRes l (none, { sA with clock := sA.clock + 0 }) =
            (some .timeOut, { sA with clock := sA.clock + 0, locals := .ln }) := by
          rw [LoopSemStateFiniteExact.cutRes]
          simp only
          rw [LoopSemStateFiniteExact.cutState_of_subset l { sA with clock := sA.clock + 0 } hsubA]
          simp [hst0, sA]
        have hrunF : LoopSemStateFiniteExact.evaluate (loopNestedSeqHOL (p ++ temps.zipWith HolLoopProg.assign les ++ [HolLoopProg.call (some (rn, l)) (some loc) temps (some (ctxt.vmax + 1, hbody, .skip, l))]))
            { t with clock := t.clock + (ck + 0) } =
            (some .timeOut, { sA with clock := sA.clock + 0, locals := .ln }) := by
          rw [hpre 0 _]
          simp only [loopNestedSeqHOL, LoopSemStateFiniteExact.evaluate_seq]
          rw [LoopSemStateFiniteExact.evaluate]
          simp only [hgk 0]
          rw [hfind]
          simp only [hrnnd, not_true_eq_false, if_false]
          rw [hc0]
        have callWork := LoopWork.callShort (s := { sA with clock := sA.clock + 0 })
          (returns := some (rn, l)) (target := some loc) (arguments := temps)
          (handler := some (ctxt.vmax + 1, hbody, .skip, l))
          (Or.inr ⟨vals, hgk 0, Or.inr ⟨_, _, hfind, Or.inr ⟨rn, l, rfl, Or.inr ⟨_, _, hc0⟩⟩⟩⟩) rfl
        obtain ⟨wl, wlWork, wlBound⟩ := finish 0 _ _ _ _ _ callWork hrunF
        refine ⟨ck + 0, some .timeOut, { sA with clock := sA.clock + 0, locals := .ln }, hrunF, h1s,
          h1m, h1g, ⟨hdf, hcodeF⟩, rfl, trivial, wl, wlWork, ?_⟩
        have := shortW hz
        omega
      · simp only [hz, if_false] at he
        have hstz : st.clock ≠ 0 := h1s.2.2.1 ▸ hz
        obtain ⟨wb, ihBody, bodyBound, handlerBound⟩ := ihb args prog _ hargs hlc
          (by simpa using hnd) hz
        have hw : (wlabWlocExact : HolWordLab 64 → WordLocW 64) = wlabWlocHOL := by
          funext v; cases v; rfl
        let T0 : LoopSemStateFiniteExact 64 F :=
          { st with locals := sptFromAList ((List.range len).zip (args.map wlabWlocHOL)),
                    clock := st.clock - 1 }
        -- `locals_rel ctxt l` at the call site (the argument temporaries are above vmax)
        have hA : crepToLoopLocalsRelExact ctxt l v1.locals sA.locals := by
          refine ⟨hl.1, hl.2.1, hsubA, fun vn val hval => ?_⟩
          obtain ⟨n, hn1, hn2, _⟩ := hl.2.2.2 vn val hval
          obtain ⟨n', hn1', _, hn3'⟩ := h1l.2.2.2 vn val hval
          have hnn : n' = n := Option.some.inj (hn1'.symm.trans hn1)
          subst hnn
          have hle := h1l.2.1 vn n' hn1'
          have hnt : n' ∉ temps := by
            simp only [temps, genTemps, List.mem_map, List.mem_range, not_exists, not_and]
            intro a _ h; omega
          refine ⟨n', hn1', hn2, ?_⟩
          show sptLookup n' (LoopSemStateFiniteExact.sptAlistInsert temps vals st.locals) = _
          rw [lookup_alist_insert_any, loopCall_holAlookup_zip_not_memP temps vals n' hnt]
          exact hn3'
        have hcutK : ∀ k, LoopSemStateFiniteExact.cutRes l (none, { sA with clock := sA.clock + k }) =
            (none, { sA with locals := sptInter sA.locals l, clock := st.clock + k - 1 }) := by
          intro k
          rw [LoopSemStateFiniteExact.cutRes]
          simp only
          rw [LoopSemStateFiniteExact.cutState_of_subset l { sA with clock := sA.clock + k } hsubA]
          simp only [LoopSemStateFiniteExact.decClock, sA,
            show ¬ st.clock + k = 0 by omega, if_false]
        have hrecK : ∀ k, ({ ({ sA with locals := sptInter sA.locals l, clock := st.clock + k - 1 } :
              LoopSemStateFiniteExact 64 F) with locals := sptFromAList ((List.range len).zip vals) } :
              LoopSemStateFiniteExact 64 F) = { T0 with clock := T0.clock + k } := by
          intro k
          simp only [sA, T0, vals, hw]
          congr 1
          omega
        have keyR : ∀ (r : CrepResultHOLExact 64) (st' : CrepSemHOLState 64 F),
            evalCrepSemHOLProgExact
                { decClockCrepSemHOL v1 with
                    locals := HolFiniteMapExact.empty.updateList (ns.zip args) } prog =
              (some r, st') →
            r ≠ .error → (∀ n, r ≠ .break n) → (∀ n, r ≠ .continue n) →
            ∃ (ck' : Nat) (t1 : LoopSemStateFiniteExact 64 F),
              LoopSemStateFiniteExact.evaluate
                  (ocompileHOLExact nctxt (listToNumSetHOLExact (List.range len)) prog)
                  { T0 with clock := T0.clock + ck' } = (resultToLoop (some r), t1) ∧
              crepToLoopStateRelExact st' t1 ∧
              crepToLoopMemRelHOLExact st'.memory t1.memory st'.memaddrs ∧
              crepToLoopGlobalsRelHOLExact st'.globals t1.globals ∧
              crepToLoopCodeRelExact ctxt st'.code t1.code ∧
              ∃ x wopt, resultToLoop (some r) = some x ∧
                LoopWork { T0 with clock := T0.clock + ck' }
                  (ocompileHOLExact nctxt (listToNumSetHOLExact (List.range len)) prog)
                  (some x, t1) wopt ∧ wopt ≤ 7 * wb := by
          intro r st' hb hre hrb hrc
          obtain ⟨ck', wbody, bodyWork, bodyWorkBound, bodyRel⟩ := ihBody T0 nctxt
            (listToNumSetHOLExact (List.range len)) (by rw [hb]; simpa using hre)
            ⟨hSc, h1m, h1g, hCc, hLc⟩
          rw [hb] at bodyRel
          rcases h2 : LoopSemStateFiniteExact.evaluate
              (compileHOLExact nctxt (listToNumSetHOLExact (List.range len)) prog)
              { T0 with clock := T0.clock + ck' } with ⟨res1', t1⟩
          rw [h2] at bodyRel bodyWork
          obtain ⟨h2s, h2m, h2g, h2c, h2r, _⟩ := bodyRel
          try dsimp only at h2s h2m h2g h2c h2r
          subst h2r
          have okR := loopCall_resultToLoop_ok hre hrb hrc
          have hopt := optimise_correct _ _ _ _ ⟨h2, okR.1, okR.2.1, okR.2.2,
            by cases r <;> simp [resultToLoop]⟩
          obtain ⟨x, hx⟩ : ∃ x, resultToLoop (some r) = some x := by cases r <;> exact ⟨_, rfl⟩
          rw [hx] at bodyWork
          obtain ⟨wopt, optWork, optBound⟩ := opt F _ _ x t1 wbody bodyWork
            (loopCall_some_ok hx hre hrb hrc).1 (loopCall_some_ok hx hre hrb hrc).2.1
            (loopCall_some_ok hx hre hrb hrc).2.2
          exact ⟨ck', t1, hopt, h2s, h2m, h2g, h2c, x, wopt, hx, optWork, by omega⟩
        split at he
        · simp only [Prod.mk.injEq] at he; exact absurd he.1.symm hne
        · simp only [Prod.mk.injEq] at he; exact absurd he.1.symm hne
        · simp only [Prod.mk.injEq] at he; exact absurd he.1.symm hne
        · rename_i _ retvs st' heq
          by_cases hlr : retvs.length = rts.length
          · simp only [hlr, ne_eq, not_true_eq_false, if_false] at he
            cases hml : rts.mapM v1.locals.lookup with
            | none => simp only [hml, Prod.mk.injEq] at he; exact absurd he.1.symm hne
            | some ws =>
            simp only [hml, Prod.mk.injEq] at he
            obtain ⟨rfl, rfl⟩ := he
            obtain ⟨nrhss, hnm, hnlen, hnl, _⟩ :=
              crepToLoop_opt_mmap_rhss_locals_rel rts ws v1 t ctxt l ⟨hml, hl⟩
            have hrn : rn = nrhss := by simp [rn, hnm]
            obtain ⟨ck', t1, hrun, h2s, h2m, h2g, h2c, x, wopt, hx, optWork, optBound⟩ :=
              keyR (.return retvs) st' heq (by simp) (by simp) (by simp)
            have hrun1 : LoopSemStateFiniteExact.evaluate
                (ocompileHOLExact nctxt (listToNumSetHOLExact (List.range len)) prog)
                { T0 with clock := T0.clock + (ck' + 1) } =
                (some (.result (retvs.map wlabWlocExact)), { t1 with clock := t1.clock + 1 }) := by
              have := LoopSemStateFiniteExact.evaluate_add_clock_eq _ _ _ _ 1 hrun (by simp [resultToLoop])
              simpa [Nat.add_assoc, resultToLoop] using this
            let X : LoopSemStateFiniteExact 64 F :=
              LoopSemStateFiniteExact.setVars rn (retvs.map wlabWlocExact)
                { t1 with clock := t1.clock + 1, locals := sptInter sA.locals l }
            have hXsub : LoopSemStateFiniteExact.sptSubsetLive l X.locals := by
              intro k hk
              have hk' : (sptLookup k l).isSome := hk
              show (sptLookup k (LoopSemStateFiniteExact.sptAlistInsert rn _ _)).isSome
              rw [lookup_alist_insert_any]
              split
              · show (sptLookup k (sptInter sA.locals l)).isSome
                rw [sptLookup_sptInter, if_pos hk']; exact hsubA k hk
              · rfl
            have hXcut : LoopSemStateFiniteExact.cutRes l (none, X) =
                (none, { t1 with locals := sptInter X.locals l }) := by
              rw [LoopSemStateFiniteExact.cutRes]
              simp only
              rw [LoopSemStateFiniteExact.cutState_of_subset l X hXsub]
              simp [LoopSemStateFiniteExact.decClock, X, LoopSemStateFiniteExact.setVars]
            have hlen2 : (retvs.map wlabWlocExact).length = rn.length := by
              simp [hrn, hnlen, hlr]
            have hrunF : LoopSemStateFiniteExact.evaluate (loopNestedSeqHOL (p ++ temps.zipWith HolLoopProg.assign les ++ [HolLoopProg.call (some (rn, l)) (some loc) temps (some (ctxt.vmax + 1, hbody, .skip, l))]))
                { t with clock := t.clock + (ck + (ck' + 1)) } =
                (none, { t1 with locals := sptInter X.locals l }) := by
              rw [hpre (ck' + 1) _]
              simp only [loopNestedSeqHOL, LoopSemStateFiniteExact.evaluate_seq]
              rw [LoopSemStateFiniteExact.evaluate]
              simp only [hgk (ck' + 1)]
              rw [hfind]
              simp only [hrnnd, not_true_eq_false, if_false]
              rw [hcutK (ck' + 1)]
              simp only
              rw [LoopSemStateFiniteExact.fix_clock_evaluate, hrecK (ck' + 1), hrun1]
              simp only [hlen2, ne_eq, not_true_eq_false, if_false]
              simp only [LoopSemStateFiniteExact.evaluate]
              have hXc := hXcut
              simp only [X] at hXc
              rw [hXc]
            have hxv : x = .result (retvs.map wlabWlocExact) := by
              simpa [resultToLoop] using hx.symm
            subst hxv
            have lifted := LoopWork.add_clock optWork 1 (by simp)
            simp only [] at lifted
            have liftState : ({ ({ T0 with clock := T0.clock + ck' } : LoopSemStateFiniteExact 64 F)
                with clock := T0.clock + ck' + 1 } : LoopSemStateFiniteExact 64 F) =
                { T0 with clock := T0.clock + (ck' + 1) } := by simp [Nat.add_assoc]
            rw [liftState, ← hrecK (ck' + 1)] at lifted
            have contWork := LoopWork.atom (p := (.skip : HolLoopProg 64)) (cost := 0)
              (s := LoopSemStateFiniteExact.setVars rn (retvs.map wlabWlocExact)
                { ({ t1 with clock := t1.clock + 1 } : LoopSemStateFiniteExact 64 F) with
                  locals := (sptInter sA.locals l) })
              rfl rfl
            have callWork := LoopWork.callRetCont (s := { sA with clock := sA.clock + (ck' + 1) })
              (exceptionName := ctxt.vmax + 1) (handlerProgram := hbody) (liveOut := l)
              (hgk (ck' + 1)) hfind hrnnd (hcutK (ck' + 1)) lifted hlen2 contWork
            obtain ⟨wl, wlWork, wlBound⟩ := finish (ck' + 1) _ _ _ _ _ callWork hrunF
            have crepBound := bodyBound _ _ heq (by intro _ _ _ c; simp at c)
            refine ⟨ck + (ck' + 1), none, { t1 with locals := sptInter X.locals l }, hrunF, h2s, h2m,
              h2g, h2c, rfl, ?_, wl, wlWork, ?_⟩
            · have := loopCall_locals_rel_after_return ctxt l v1.locals sA.locals rts rn retvs hA
                (hrn ▸ hnm) (hrn ▸ hnl) hnd hrnnd hlr
              simpa [X, LoopSemStateFiniteExact.setVars, localsResultRel] using this
            · have l2 : retvs.length = rn.length := by simpa using hlen2
              have l3 : rn.length = nrhss.length := by rw [hrn]
              simp only [crepCallPayloadWords] at crepBound
              omega
          · simp only [hlr, ne_eq, not_false_eq_true, if_true, Prod.mk.injEq] at he
            exact absurd he.1.symm hne
        · rename_i _ eid st' heq
          obtain ⟨ck', t1, hrun, h2s, h2m, h2g, h2c, x, wopt, hx, optWork, optBound⟩ :=
            keyR (.exception eid) st' heq (by simp) (by simp) (by simp)
          have hxv : x = .exception (.word eid) := by simpa [resultToLoop] using hx.symm
          subst hxv
          cases hdl with
          | none =>
            simp only [Prod.mk.injEq] at he
            obtain ⟨rfl, rfl⟩ := he
            have hrunF : LoopSemStateFiniteExact.evaluate (loopNestedSeqHOL (p ++ temps.zipWith HolLoopProg.assign les ++ [HolLoopProg.call (some (rn, l)) (some loc) temps (some (ctxt.vmax + 1, hbody, .skip, l))]))
                { t with clock := t.clock + (ck + ck') } =
                (some (.exception (.word eid)), LoopSemStateFiniteExact.callEnv []
                  (LoopSemStateFiniteExact.setVar (ctxt.vmax + 1) (.word eid)
                    { t1 with locals := sptInter sA.locals l })) := by
              rw [hpre (ck') _]
              simp only [loopNestedSeqHOL, LoopSemStateFiniteExact.evaluate_seq]
              rw [LoopSemStateFiniteExact.evaluate]
              simp only [hgk (ck')]
              rw [hfind]
              simp only [hrnnd, not_true_eq_false, if_false]
              rw [hcutK (ck')]
              simp only
              rw [LoopSemStateFiniteExact.fix_clock_evaluate, hrecK (ck'), hrun]
              simp only [resultToLoop, hbody, LoopSemStateFiniteExact.evaluate,
                LoopSemStateFiniteExact.setVar, sptLookup_sptInsert, if_true]
              rfl
            rw [← hrecK ck'] at optWork
            have handleWork := LoopWork.atom (p := hbody) (cost := 1) rfl
              (s := LoopSemStateFiniteExact.setVar (ctxt.vmax + 1) (.word eid)
                { t1 with locals := (sptInter sA.locals l) }) rfl
            have callWork := LoopWork.callHandle (s := { sA with clock := sA.clock + ck' })
              (continuation := .skip) (liveOut := l)
              (hgk ck') hfind hrnnd (hcutK ck') optWork handleWork
            obtain ⟨wl, wlWork, wlBound⟩ := finish ck' _ _ _ _ _ callWork hrunF
            have crepBound := bodyBound _ _ heq (by intro e r h c; simp)
            refine ⟨ck + ck', some (.exception (.word eid)), LoopSemStateFiniteExact.callEnv []
              (LoopSemStateFiniteExact.setVar (ctxt.vmax + 1) (.word eid)
                { t1 with locals := sptInter sA.locals l }), hrunF, h2s, h2m, h2g, h2c, rfl, trivial,
              wl, wlWork, ?_⟩
            simp only [crepCallPayloadWords] at crepBound
            omega
          | some hq =>
            obtain ⟨eid', hp⟩ := hq
            by_cases hee : eid = eid'
            · subst hee
              simp only [if_true] at he
              let Z : LoopSemStateFiniteExact 64 F :=
                { t1 with locals := sptInsert (ctxt.vmax + 1) (.word eid) (sptInter sA.locals l) }
              have hZl : crepToLoopLocalsRelExact ctxt l v1.locals Z.locals :=
                crepToLoopLocalsRelExact_insert_gt_vmax ctxt l v1.locals _ (ctxt.vmax + 1) _
                  (loopCall_locals_rel_inter ctxt l v1.locals sA.locals hA) (Nat.lt_succ_self _)
              obtain ⟨wh, ihHandler, handlerCrepBound⟩ := handlerBound st' eid rts hp heq rfl
              obtain ⟨ck'', whl, hWork, hWBound, hRel⟩ :=
                ihHandler Z (by rw [he]; exact hne) ⟨h2s, h2m, h2g, h2c, hZl⟩
              rw [he] at hRel
              rcases h3 : LoopSemStateFiniteExact.evaluate (compileHOLExact ctxt l hp)
                  { Z with clock := Z.clock + ck'' } with ⟨res1, t2⟩
              rw [h3] at hRel hWork
              obtain ⟨h3s, h3m, h3g, h3c, h3r, h3l⟩ := hRel
              try dsimp only at h3s h3m h3g h3c h3r h3l
              -- executed work of the compiled handler dispatch from a clock extension `J ≥ 1`
              have handlerDispatch : ∀ (J : Nat) (o : Option (LoopSemStateFiniteExact.LoopResultExact 64) ×
                    LoopSemStateFiniteExact 64 F) (wc : Nat), 1 ≤ J →
                  LoopWork { Z with clock := Z.clock + (J - 1) } (compileHOLExact ctxt l hp) o wc →
                  LoopWork (LoopSemStateFiniteExact.setVar (ctxt.vmax + 1) (.word eid)
                    { t1 with clock := t1.clock + J, locals := sptInter sA.locals l }) hbody
                    (LoopSemStateFiniteExact.cutRes l o) (2 + (1 + wc)) := by
                intro J o wc hJ hpWork
                have tickRun : LoopSemStateFiniteExact.evaluate .tick
                    (LoopSemStateFiniteExact.setVar (ctxt.vmax + 1) (.word eid)
                      { t1 with clock := t1.clock + J, locals := sptInter sA.locals l }) =
                    (none, { Z with clock := Z.clock + (J - 1) }) := by
                  rw [LoopSemStateFiniteExact.evaluate]
                  simp only [LoopSemStateFiniteExact.setVar, show ¬ t1.clock + J = 0 by omega, if_false]
                  simp only [LoopSemStateFiniteExact.decClock, Z, Prod.mk.injEq, true_and]
                  congr 1
                  omega
                have tickWork := LoopWork.atom (cost := 1) rfl tickRun
                have seqWork := LoopWork.seqNext tickWork hpWork
                have chosen : (if Compiler.Encoders.Asm.wordCmpHOL .notEqual eid eid then
                    (HolLoopProg.raise (ctxt.vmax + 1) : HolLoopProg 64)
                    else .seq .tick (compileHOLExact ctxt l hp)) =
                    .seq .tick (compileHOLExact ctxt l hp) := by
                  simp [Compiler.Encoders.Asm.wordCmpHOL]
                exact LoopWork.iteBranch (x := eid) (y := eid)
                  (by simp [LoopSemStateFiniteExact.setVar, sptLookup_sptInsert]) rfl
                  (by rw [chosen]; exact seqWork)
              -- the handler body from a clock extension `J ≥ 1`
              have hbodyJ : ∀ J, 1 ≤ J → LoopSemStateFiniteExact.evaluate hbody
                  (LoopSemStateFiniteExact.setVar (ctxt.vmax + 1) (.word eid)
                    { t1 with clock := t1.clock + J, locals := sptInter sA.locals l }) =
                  LoopSemStateFiniteExact.cutRes l
                    (LoopSemStateFiniteExact.evaluate (compileHOLExact ctxt l hp)
                      { Z with clock := Z.clock + (J - 1) }) := by
                intro J hJ
                simp only [hbody]
                rw [LoopSemStateFiniteExact.evaluate]
                simp only [LoopSemStateFiniteExact.setVar, sptLookup_sptInsert, if_true,
                  LoopSemStateFiniteExact.getVarImm, Compiler.Encoders.Asm.wordCmpHOL,
                  beq_self_eq_true, Bool.not_true, Bool.false_eq_true, if_false]
                rw [LoopSemStateFiniteExact.evaluate_seq]
                rw [LoopSemStateFiniteExact.evaluate]
                simp only [show ¬ t1.clock + J = 0 by omega, if_false]
                congr 3
                simp only [LoopSemStateFiniteExact.decClock, Z]
                congr 1
                omega
              cases res with
              | none =>
                have hr1 : res1 = none := by simpa [resultToLoop] using h3r
                subst hr1
                have h3l' : crepToLoopLocalsRelExact ctxt l s1.locals t2.locals := h3l
                have hrunK : LoopSemStateFiniteExact.evaluate
                    (ocompileHOLExact nctxt (listToNumSetHOLExact (List.range len)) prog)
                    { T0 with clock := T0.clock + (ck' + (ck'' + 3)) } =
                    (some (.exception (.word eid)), { t1 with clock := t1.clock + (ck'' + 3) }) := by
                  have := LoopSemStateFiniteExact.evaluate_add_clock_eq _ _ _ _ (ck'' + 3) hrun
                    (by simp [resultToLoop])
                  simpa [Nat.add_assoc, resultToLoop] using this
                have h3k : LoopSemStateFiniteExact.evaluate (compileHOLExact ctxt l hp)
                    { Z with clock := Z.clock + (ck'' + 3 - 1) } =
                    (none, { t2 with clock := t2.clock + 2 }) := by
                  have := LoopSemStateFiniteExact.evaluate_add_clock_eq _ _ _ _ 2 h3 (by simp)
                  simpa [Nat.add_assoc] using this
                have hsub2 : LoopSemStateFiniteExact.sptSubsetLive l t2.locals := h3l'.2.2.1
                have hc1 : LoopSemStateFiniteExact.cutRes l (none, { t2 with clock := t2.clock + 2 }) =
                    (none, { t2 with locals := sptInter t2.locals l, clock := t2.clock + 1 }) := by
                  rw [LoopSemStateFiniteExact.cutRes]
                  simp only
                  rw [LoopSemStateFiniteExact.cutState_of_subset l { t2 with clock := t2.clock + 2 } hsub2]
                  simp [LoopSemStateFiniteExact.decClock]
                have hsub3 : LoopSemStateFiniteExact.sptSubsetLive l (sptInter t2.locals l) :=
                  (loopCall_locals_rel_inter ctxt l s1.locals t2.locals h3l').2.2.1
                have hc2 : LoopSemStateFiniteExact.cutRes l
                    (none, { t2 with locals := sptInter t2.locals l, clock := t2.clock + 1 }) =
                    (none, { t2 with locals := sptInter (sptInter t2.locals l) l }) := by
                  rw [LoopSemStateFiniteExact.cutRes]
                  simp only
                  rw [LoopSemStateFiniteExact.cutState_of_subset l
                    { t2 with locals := sptInter t2.locals l, clock := t2.clock + 1 } hsub3]
                  simp [LoopSemStateFiniteExact.decClock]
                have hrunF : LoopSemStateFiniteExact.evaluate (loopNestedSeqHOL (p ++ temps.zipWith HolLoopProg.assign les ++ [HolLoopProg.call (some (rn, l)) (some loc) temps (some (ctxt.vmax + 1, hbody, .skip, l))]))
                    { t with clock := t.clock + (ck + (ck' + (ck'' + 3))) } =
                    (none, { t2 with locals := sptInter (sptInter t2.locals l) l }) := by
                  rw [hpre (ck' + (ck'' + 3)) _]
                  simp only [loopNestedSeqHOL, LoopSemStateFiniteExact.evaluate_seq]
                  rw [LoopSemStateFiniteExact.evaluate]
                  simp only [hgk (ck' + (ck'' + 3))]
                  rw [hfind]
                  simp only [hrnnd, not_true_eq_false, if_false]
                  rw [hcutK (ck' + (ck'' + 3))]
                  simp only
                  rw [LoopSemStateFiniteExact.fix_clock_evaluate, hrecK (ck' + (ck'' + 3)), hrunK]
                  simp only
                  rw [hbodyJ (ck'' + 3) (by omega), h3k, hc1, hc2]
                  simp only [LoopSemStateFiniteExact.evaluate]
                have bodyLifted := LoopWork.add_clock optWork (ck'' + 3) (by simp)
                simp only [] at bodyLifted
                have liftState : ({ ({ T0 with clock := T0.clock + ck' } : LoopSemStateFiniteExact 64 F)
                    with clock := T0.clock + ck' + (ck'' + 3) } : LoopSemStateFiniteExact 64 F) =
                    { T0 with clock := T0.clock + (ck' + (ck'' + 3)) } := by simp [Nat.add_assoc]
                rw [liftState, ← hrecK (ck' + (ck'' + 3))] at bodyLifted
                have hpLifted := LoopWork.add_clock hWork 2 (by simp)
                simp only [] at hpLifted
                have hpState : ({ ({ Z with clock := Z.clock + ck'' } : LoopSemStateFiniteExact 64 F)
                    with clock := Z.clock + ck'' + 2 } : LoopSemStateFiniteExact 64 F) =
                    { Z with clock := Z.clock + (ck'' + 3 - 1) } := by
                  rw [show ck'' + 3 - 1 = ck'' + 2 by omega, Nat.add_assoc]
                rw [hpState] at hpLifted
                have handleWork := handlerDispatch (ck'' + 3) _ _ (by omega) hpLifted
                have callWork := LoopWork.callHandle
                  (s := { sA with clock := sA.clock + (ck' + (ck'' + 3)) })
                  (continuation := .skip) (liveOut := l)
                  (hgk (ck' + (ck'' + 3))) hfind hrnnd (hcutK (ck' + (ck'' + 3))) bodyLifted handleWork
                obtain ⟨wl, wlWork, wlBound⟩ := finish (ck' + (ck'' + 3)) _ _ _ _ _ callWork hrunF
                refine ⟨ck + (ck' + (ck'' + 3)), none,
                  { t2 with locals := sptInter (sptInter t2.locals l) l }, hrunF, h3s, h3m, h3g, h3c,
                  rfl, loopCall_locals_rel_inter ctxt l _ _ (loopCall_locals_rel_inter ctxt l _ _ h3l'),
                  wl, wlWork, by omega⟩
              | some r =>
                obtain ⟨x, hx⟩ : ∃ x, res1 = some x := by
                  cases r <;> simp only [resultToLoop] at h3r <;> exact ⟨_, h3r⟩
                have hrunK : LoopSemStateFiniteExact.evaluate
                    (ocompileHOLExact nctxt (listToNumSetHOLExact (List.range len)) prog)
                    { T0 with clock := T0.clock + (ck' + (ck'' + 1)) } =
                    (some (.exception (.word eid)), { t1 with clock := t1.clock + (ck'' + 1) }) := by
                  have := LoopSemStateFiniteExact.evaluate_add_clock_eq _ _ _ _ (ck'' + 1) hrun
                    (by simp [resultToLoop])
                  simpa [Nat.add_assoc, resultToLoop] using this
                have h3k : LoopSemStateFiniteExact.evaluate (compileHOLExact ctxt l hp)
                    { Z with clock := Z.clock + (ck'' + 1 - 1) } = (res1, t2) := by
                  simpa using h3
                have hrunF : LoopSemStateFiniteExact.evaluate (loopNestedSeqHOL (p ++ temps.zipWith HolLoopProg.assign les ++ [HolLoopProg.call (some (rn, l)) (some loc) temps (some (ctxt.vmax + 1, hbody, .skip, l))]))
                    { t with clock := t.clock + (ck + (ck' + (ck'' + 1))) } = (res1, t2) := by
                  rw [hpre (ck' + (ck'' + 1)) _]
                  simp only [loopNestedSeqHOL, LoopSemStateFiniteExact.evaluate_seq]
                  rw [LoopSemStateFiniteExact.evaluate]
                  simp only [hgk (ck' + (ck'' + 1))]
                  rw [hfind]
                  simp only [hrnnd, not_true_eq_false, if_false]
                  rw [hcutK (ck' + (ck'' + 1))]
                  simp only
                  rw [LoopSemStateFiniteExact.fix_clock_evaluate, hrecK (ck' + (ck'' + 1)), hrunK]
                  simp only
                  rw [hbodyJ (ck'' + 1) (by omega), h3k, hx]
                  rfl
                have bodyLifted := LoopWork.add_clock optWork (ck'' + 1) (by simp)
                simp only [] at bodyLifted
                have liftState : ({ ({ T0 with clock := T0.clock + ck' } : LoopSemStateFiniteExact 64 F)
                    with clock := T0.clock + ck' + (ck'' + 1) } : LoopSemStateFiniteExact 64 F) =
                    { T0 with clock := T0.clock + (ck' + (ck'' + 1)) } := by simp [Nat.add_assoc]
                rw [liftState, ← hrecK (ck' + (ck'' + 1))] at bodyLifted
                have hpState : ({ Z with clock := Z.clock + ck'' } : LoopSemStateFiniteExact 64 F) =
                    { Z with clock := Z.clock + (ck'' + 1 - 1) } := by simp
                rw [hpState] at hWork
                have handleWork := handlerDispatch (ck'' + 1) _ _ (by omega) hWork
                have callWork := LoopWork.callHandle
                  (s := { sA with clock := sA.clock + (ck' + (ck'' + 1)) })
                  (continuation := .skip) (liveOut := l)
                  (hgk (ck' + (ck'' + 1))) hfind hrnnd (hcutK (ck' + (ck'' + 1))) bodyLifted handleWork
                obtain ⟨wl, wlWork, wlBound⟩ := finish (ck' + (ck'' + 1)) _ _ _ _ _ callWork hrunF
                refine ⟨ck + (ck' + (ck'' + 1)), res1, t2, hrunF, h3s, h3m, h3g, h3c, h3r, h3l,
                  wl, wlWork, by omega⟩
            · simp only [hee, if_false, Prod.mk.injEq] at he
              obtain ⟨rfl, rfl⟩ := he
              have hrunF : LoopSemStateFiniteExact.evaluate (loopNestedSeqHOL (p ++ temps.zipWith HolLoopProg.assign les ++ [HolLoopProg.call (some (rn, l)) (some loc) temps (some (ctxt.vmax + 1, hbody, .skip, l))]))
                  { t with clock := t.clock + (ck + ck') } =
                  (some (.exception (.word eid)), LoopSemStateFiniteExact.callEnv []
                    (LoopSemStateFiniteExact.setVar (ctxt.vmax + 1) (.word eid)
                      { t1 with locals := sptInter sA.locals l })) := by
                rw [hpre (ck') _]
                simp only [loopNestedSeqHOL, LoopSemStateFiniteExact.evaluate_seq]
                rw [LoopSemStateFiniteExact.evaluate]
                simp only [hgk (ck')]
                rw [hfind]
                simp only [hrnnd, not_true_eq_false, if_false]
                rw [hcutK (ck')]
                simp only
                rw [LoopSemStateFiniteExact.fix_clock_evaluate, hrecK (ck'), hrun]
                have hb : (eid == eid') = false := beq_eq_false_iff_ne.mpr hee
                simp only [resultToLoop, hbody, LoopSemStateFiniteExact.evaluate,
                  LoopSemStateFiniteExact.setVar, sptLookup_sptInsert, if_true,
                  LoopSemStateFiniteExact.getVarImm, Compiler.Encoders.Asm.wordCmpHOL, hb,
                  Bool.not_false]
                rfl
              rw [← hrecK ck'] at optWork
              have chosen : (if Compiler.Encoders.Asm.wordCmpHOL .notEqual eid eid' then
                  (HolLoopProg.raise (ctxt.vmax + 1) : HolLoopProg 64)
                  else .seq .tick (compileHOLExact ctxt l hp)) = .raise (ctxt.vmax + 1) := by
                have hb : (eid == eid') = false := beq_eq_false_iff_ne.mpr hee
                have hcmp : Compiler.Encoders.Asm.wordCmpHOL .notEqual eid eid' = true := by
                  simpa [Compiler.Encoders.Asm.wordCmpHOL] using hee
                rw [if_pos hcmp]
              have raiseWork := LoopWork.atom (p := (.raise (ctxt.vmax + 1) : HolLoopProg 64))
                (cost := 1) rfl
                (s := LoopSemStateFiniteExact.setVar (ctxt.vmax + 1) (.word eid)
                  { t1 with locals := (sptInter sA.locals l) }) rfl
              have handleWork := LoopWork.iteBranch (live := l) (x := eid) (y := eid')
                (s := LoopSemStateFiniteExact.setVar (ctxt.vmax + 1) (.word eid)
                  { t1 with locals := (sptInter sA.locals l) })
                (operator := .notEqual) (register := ctxt.vmax + 1) (right := .imm eid')
                (yes := (.raise (ctxt.vmax + 1) : HolLoopProg 64))
                (no := .seq .tick (compileHOLExact ctxt l hp))
                (by simp [LoopSemStateFiniteExact.setVar, sptLookup_sptInsert]) rfl
                (by rw [chosen]; exact raiseWork)
              have callWork := LoopWork.callHandle (s := { sA with clock := sA.clock + ck' })
                (handlerProgram := hbody) (continuation := .skip) (liveOut := l)
                (hgk ck') hfind hrnnd (hcutK ck') optWork handleWork
              obtain ⟨wl, wlWork, wlBound⟩ := finish ck' _ _ _ _ _ callWork hrunF
              have crepBound := bodyBound _ _ heq (by
                intro e r h hex heqc
                simp only [Option.some.injEq, CrepResultHOLExact.exception.injEq] at hex
                subst hex
                simp only [Option.some.injEq, Prod.mk.injEq] at heqc
                exact hee heqc.2.1.symm)
              refine ⟨ck + ck', some (.exception (.word eid)), LoopSemStateFiniteExact.callEnv []
                (LoopSemStateFiniteExact.setVar (ctxt.vmax + 1) (.word eid)
                  { t1 with locals := sptInter sA.locals l }), hrunF, h2s, h2m, h2g, h2c, rfl, trivial,
                wl, wlWork, ?_⟩
              simp only [crepCallPayloadWords] at crepBound
              omega
        · rename_i _ r' st' hn hb hcn hr hx heq
          simp only [Prod.mk.injEq] at he
          obtain ⟨rfl, rfl⟩ := he
          rcases r' with _ | r
          · exact absurd rfl hn
          have hre : r ≠ .error := fun h => hne (by rw [h])
          obtain ⟨ck', t1, hrun, h2s, h2m, h2g, h2c, x, wopt, hxr, optWork, optBound⟩ :=
            keyR r st' heq hre (fun n h => hb n (by rw [h])) (fun n h => hcn n (by rw [h]))
          have hrunF : LoopSemStateFiniteExact.evaluate (loopNestedSeqHOL (p ++ temps.zipWith HolLoopProg.assign les ++ [HolLoopProg.call (some (rn, l)) (some loc) temps (some (ctxt.vmax + 1, hbody, .skip, l))]))
              { t with clock := t.clock + (ck + ck') } = (resultToLoop (some r), t1) := by
            rw [hpre ck' _]
            simp only [loopNestedSeqHOL, LoopSemStateFiniteExact.evaluate_seq]
            rw [LoopSemStateFiniteExact.evaluate]
            simp only [hgk ck']
            rw [hfind]
            simp only [hrnnd, not_true_eq_false, if_false]
            rw [hcutK ck']
            simp only
            rw [LoopSemStateFiniteExact.fix_clock_evaluate, hrecK ck', hrun]
            cases r with
            | «return» v => exact absurd rfl (hr v)
            | exception v => exact absurd rfl (hx v)
            | «break» n => exact absurd rfl (hb n)
            | «continue» n => exact absurd rfl (hcn n)
            | error => exact absurd rfl hre
            | _ => rfl
          rw [← hrecK ck'] at optWork
          have plain : loopRetPlain (some x) rn (some (ctxt.vmax + 1, hbody, .skip, l)) := by
            cases r <;> first | exact absurd rfl (hr _) | exact absurd rfl (hx _) | exact absurd rfl (hb _) | exact absurd rfl (hcn _) | exact absurd rfl hre | (simp only [resultToLoop, Option.some.injEq] at hxr; subst hxr; simp [loopRetPlain])
          have exitEq : ∀ (e : LoopSemStateFiniteExact 64 F),
              loopRetExit (some x) t1 e rn = (resultToLoop (some r), t1) := by
            intro e
            cases r <;> first | exact absurd rfl (hr _) | exact absurd rfl (hx _) | exact absurd rfl (hb _) | exact absurd rfl (hcn _) | exact absurd rfl hre | (simp only [resultToLoop, Option.some.injEq] at hxr; subst hxr; simp [loopRetExit, resultToLoop])
          have wordsZero : loopRetWords (some x) = 0 := by
            cases r <;> first | exact absurd rfl (hr _) | exact absurd rfl (hx _) | exact absurd rfl (hb _) | exact absurd rfl (hcn _) | exact absurd rfl hre | (simp only [resultToLoop, Option.some.injEq] at hxr; subst hxr; simp [loopRetWords])
          have callWork := LoopWork.callRet (s := { sA with clock := sA.clock + ck' })
            (hgk ck') hfind hrnnd (hcutK ck') optWork plain
          rw [exitEq, wordsZero] at callWork
          obtain ⟨wl, wlWork, wlBound⟩ := finish ck' _ _ _ _ _ callWork hrunF
          have crepBound := bodyBound _ _ heq (by
            intro e rts' hp' h
            exact (hx e h).elim)
          have payloadZero : crepCallPayloadWords (some r) = 0 := by
            cases r <;> first | rfl | exact absurd rfl (hr _)
          refine ⟨ck + ck', resultToLoop (some r), t1, hrunF, h2s, h2m, h2g, h2c, rfl, ?_,
            wl, wlWork, ?_⟩
          · cases r <;> first | exact True.intro | exact (hb _ rfl).elim | exact (hcn _ rfl).elim | exact (hre rfl).elim
          · rw [payloadZero] at crepBound
            omega
    · simp only [hnd, not_false_eq_true, if_true, Prod.mk.injEq] at he
      exact absurd he.1.symm hne

#print axioms call_loop_paid

end InitECandidate.Runtime.FineCost
