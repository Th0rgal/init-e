import InitECandidate.Runtime.StackPathWorkLoop
import InitECandidate.Runtime.StackToLabCall
import Flapjack.Compiler.Backend.StackToLab.Proofs.FlattenCorrect.Call

namespace InitECandidate.Runtime.StackToLab
open Flapjack Flapjack.Compiler.Backend.LabLang Flapjack.Compiler.Backend.LabSem
open Flapjack.Compiler.Encoders.Asm Flapjack.Compiler.Backend.StackLang
open Flapjack.Compiler.Backend.StackToLab.Proofs.CodeInstalled
open Flapjack.Compiler.Backend.StackToLab.Proofs.StateRel
open Flapjack.Compiler.Backend.StackToLab.Proofs.FlattenHelpers
open Flapjack.Compiler.Backend.StackToLab.Proofs.FlattenCorrect
open Flapjack.Compiler.Backend.StackToLab.Proofs

section
variable {width : Nat} [NeZero width] {C F : Type}
theorem pathWork_tailCall_bound (s1 : StackSemStateFiniteExact width C F) (dest : Nat ⊕ Nat)
    (handler : Option (HolProg width × Nat × Nat))
    (ih : ∀ (p : HolProg width) (s : StackSemStateFiniteExact width C F),
      MeasureLt p s (.call none dest handler) s1 → BoundedFlattenProp p s (pathWork p s)) :
    BoundedFlattenProp (.call none dest handler) s1 (pathWork (.call none dest handler) s1) := by
  rintro t r s2 n l cs bs t1 ⟨ev, nerr, rel, -, inst, -⟩
  rw [StackSemEvaluate.evaluate_call] at ev
  simp only at ev
  have fetch : asmFetchAux t1.pc t1.code = some (Flapjack.Compiler.Backend.StackToLab.compileJumpHOL dest) :=
    fetchSingle (Prelude.notIsLabelCompileJump dest)
      (by simpa [Flapjack.Compiler.Backend.StackToLab.flattenHOL, appListAppendList] using inst)
  have err : ∀ {x : StackSemStateFiniteExact width C F},
      (some StackSemResult.error, x) = (r, s2) → False := fun e => by
    simp only [Prod.mk.injEq] at e; exact nerr e.1.symm
  have clk := relClock rel
  rcases hfind : StackSemControl.findCode dest s1.regs s1.code with _ | prog
  · rw [hfind] at ev; exact (err ev).elim
  rw [hfind] at ev
  simp only at ev
  rcases handler with _ | hd
  swap; · exact (err ev).elim
  simp only at ev
  obtain ⟨d, pc', -, entry, caP, instP, step⟩ :=
    compileJumpEnter (fun r v h => InstCorrect.regOfLookup rel h) rel fetch hfind
  by_cases h0 : s1.clock = 0
  · rw [if_pos h0] at ev
    simp only [Prod.mk.injEq] at ev
    obtain ⟨rfl, rfl⟩ := ev
    refine ⟨0, Nat.zero_le _, t1, fun _ => by simp, rfl, rfl, rfl, rfl, rfl, List.prefix_refl _, ?_, ?_⟩
    · simp [StackSemStateOps.emptyEnv, relFfi rel]
    · omega
  rw [if_neg h0, StackSemEvaluateClock.fixClockEvaluate] at ev
  rcases e2 : StackSemEvaluate.evaluate (prog, StackSemStateOps.decClock s1) with ⟨res, s'⟩
  rw [e2] at ev
  simp only at ev
  by_cases hbad : StackSemControl.badFunReturn res = true
  · rw [if_pos hbad] at ev; exact (err ev).elim
  rw [if_neg hbad] at ev
  simp only [Prod.mk.injEq] at ev
  obtain ⟨rfl, rfl⟩ := ev
  obtain ⟨x', rfl⟩ := notBadFunReturnImpSome _ hbad
  have rel' : stateRel (StackSemStateOps.decClock s1)
      { t1 with pc := pc', clock := t1.clock - 1 } := StateRel.stateRelDecClock rel
  have lt : MeasureLt prog (StackSemStateOps.decClock s1) (.call none dest none) s1 :=
    .inl (by simp [StackSemStateOps.decClock]; omega)
  have ph := ih prog _ lt true (some x') s' d (Flapjack.Compiler.Backend.StackAlloc.nextLabHOL prog 2) [] []
    { t1 with pc := pc', clock := t1.clock - 1 }
    ⟨e2, nerr, rel', caP, instP, by simp [entry]⟩
  refine boundedFlattenConcl_mono (a := 0 + pathWork prog (StackSemStateOps.decClock s1)) ?_ ?_
  · simp only [pathWork, if_neg h0, hfind]
    omega
  · exact boundedComposeSome 0 (pathWork prog (StackSemStateOps.decClock s1)) (by decide) (runEnter (by omega) step) rfl rfl rfl rfl rfl
      (List.prefix_refl _)
      (boundedFlattenConclResult (budget := pathWork prog (StackSemStateOps.decClock s1)) (p' := prog) (t' := true) (l' := 0) (h := ph) rfl
        (resultViewIndep hbad _ _ _ _ _ _))
/-- `Call` case with a return handler. -/
theorem pathWork_returnCall_bound (s1 : StackSemStateFiniteExact width C F) (rp : HolProg width)
    (link l1 l2 : Nat) (dest : Nat ⊕ Nat) (handler : Option (HolProg width × Nat × Nat))
    (ih : ∀ (p : HolProg width) (s : StackSemStateFiniteExact width C F),
      MeasureLt p s (.call (some (rp, link, l1, l2)) dest handler) s1 → BoundedFlattenProp p s (pathWork p s)) :
    BoundedFlattenProp (.call (some (rp, link, l1, l2)) dest handler) s1 (pathWork (.call (some (rp, link, l1, l2)) dest handler) s1) := by
  rintro t r s2 n l cs bs t1 ⟨ev, nerr, rel, ca, inst, labs⟩
  rw [StackSemEvaluate.evaluate_call] at ev
  simp only at ev
  have err : ∀ {x : StackSemStateFiniteExact width C F},
      (some StackSemResult.error, x) = (r, s2) → False := fun e => by
    simp only [Prod.mk.injEq] at e; exact nerr e.1.symm
  have clk := relClock rel
  unfold Flapjack.Compiler.Backend.StackProps.callArgs at ca
  simp only at ca
  have caR := ca.1
  have caH := ca.2.2
  rcases h1 : Flapjack.Compiler.Backend.StackToLab.flattenHOL false rp n l cs bs with ⟨xs, nr1, m1⟩
  obtain ⟨rest, hflat, hrest⟩ := callRetPrelude (t := t) (link := link) (l1 := l1) (l2 := l2)
    (dest := dest) (handler := handler) h1
  have inst0 := inst
  rw [hflat] at inst
  obtain ⟨fetchA, inst2⟩ := lineAt rfl inst
  obtain ⟨fetchB, inst3⟩ := lineAt (Prelude.notIsLabelCompileJump dest) inst2
  obtain ⟨locL, inst4⟩ := labelAt inst3
  obtain ⟨instXs, instRest⟩ := codeInstalledAppendImp _ _ _ _ inst4
  rcases hfind : StackSemControl.findCode dest (s1.regs.eraseEq link) s1.code with _ | prog
  · rw [hfind] at ev; exact (err ev).elim
  rw [hfind] at ev
  simp only at ev
  by_cases h0 : s1.clock = 0
  · rw [if_pos h0] at ev
    simp only [Prod.mk.injEq] at ev
    obtain ⟨rfl, rfl⟩ := ev
    refine ⟨0, Nat.zero_le _, t1, fun _ => by simp, rfl, rfl, rfl, rfl, rfl, List.prefix_refl _, ?_, ?_⟩
    · simp [StackSemStateOps.emptyEnv, relFfi rel]
    · omega
  rw [if_neg h0] at ev
  rcases e2 : StackSemEvaluate.evaluate (prog, StackSemStateOps.decClock
    (StackSemStateOps.setVar link (.loc l1 l2) s1)) with ⟨res0, s2'⟩
  have ev' := callRetEval e2 ev
  obtain ⟨d, pc', tE, run1, f1, f2, f3, f4, f5, fcode, fpc, relE, entry, caP, instP⟩ :=
    callEnter rel h0 fetchA fetchB (by simpa using locL) hfind
  have nerr0 : res0 ≠ some .error := by
    rintro rfl; exact err ev'
  have lt : MeasureLt prog (StackSemStateOps.decClock
      (StackSemStateOps.setVar link (.loc l1 l2) s1)) (.call (some (rp, link, l1, l2)) dest
        handler) s1 := .inl (setVarDecClockLt h0)
  let budget := pathWork prog (StackSemStateOps.decClock (StackSemStateOps.setVar link (.loc l1 l2) s1)) + pathWork rp s2' +
    (match (generalizing := false) handler with | none => 0 | some (hp, _, _) => pathWork hp s2')
  have workEq : pathWork (.call (some (rp, link, l1, l2)) dest handler) s1 = 2 * budget + 2 := by
    rw [pathWork, if_neg h0, hfind]
    dsimp only
    rw [StackSemEvaluateClock.fixClockEvaluate, e2]
    dsimp only [budget]
    cases handler <;> rfl
  rw [workEq]
  have calleeLe : pathWork prog (StackSemStateOps.decClock (StackSemStateOps.setVar link (.loc l1 l2) s1)) ≤ budget := by
    dsimp only [budget]
    omega
  have returnLe : pathWork rp s2' ≤ budget := by
    dsimp only [budget]
    omega
  have phRaw := ih prog _ lt true res0 s2' d (Flapjack.Compiler.Backend.StackAlloc.nextLabHOL prog 2) [] [] tE
    ⟨e2, nerr0, relE, by rw [f1, f2, f3, f4, f5]; exact caP, by rw [fcode, fpc]; exact instP,
      by simp [fcode, entry]⟩
  have ph := boundedFlattenConcl_mono calleeLe phRaw
  have hs2clk : s2'.clock < s1.clock :=
    Nat.lt_of_le_of_lt (StackSemEvaluateClock.evaluateClock _ _ _ _ e2) (setVarDecClockLt h0)
  have prop := fun (x : StackSemResult width) (hind : ∀ cs bs cs' bs' : List Nat, ∀ m m',
      resultView x m cs bs = resultView x m' cs' bs')
      (phx : BoundedFlattenConcl prog true (some x) s2' d (Flapjack.Compiler.Backend.StackAlloc.nextLabHOL prog 2) [] [] tE budget) =>
    boundedCallPropagate (p' := .call (some (rp, link, l1, l2)) dest handler) (t := t) (n := n) (l := l)
      (cs := cs) (bs := bs) budget run1 f1 f2 f3 f4 f5 fcode hind phx
  rcases res0 with _ | x
  · exact (err ev').elim
  rcases x with v | v | k | k | v | _ | o | _
  · -- the callee returned
    simp only at ev'
    by_cases hv : v = .loc l1 l2
    swap; · rw [if_pos hv] at ev'; exact (err ev').elim
    rw [if_neg (not_not.mpr hv)] at ev'
    subst hv
    obtain ⟨ck', calleeBound, t3, run3, g1, g2, g3, g4, g5, pre3, hw⟩ :=
      boundedFlattenConclVloc (n1 := l1) (n2 := l2) budget rfl rfl ph
    rw [fcode] at pre3
    obtain ⟨hpc3, rel3⟩ := hw (t1.pc + 1 + 1) (locToPcIsPrefix _ _ _ _ _ ⟨locL, pre3⟩)
    have rh := ih rp s2' (.inl hs2clk) false r s2 n l cs bs t3
      ⟨ev', nerr, rel3, by rw [g1, g2, g3, g4, g5, f1, f2, f3, f4, f5]; exact caR,
        by rw [← hpc3, h1]; exact codeInstalledIsPrefix _ _ _ _ ⟨instXs, pre3⟩,
        fun k hk => isSomeLocToPcPrefix ⟨labs k hk, pre3⟩⟩
    have rh := boundedFlattenConcl_mono returnLe rh
    have run13 := chainRun run1 run3
    rcases handler with _ | ⟨hp, hs, hl⟩
    · rw [hrest rfl] at hflat
      refine callCompose budget (by omega) run13 (by rw [g1, f1]) (by rw [g2, f2]) (by rw [g3, f3])
        (by rw [g4, f4]) (by rw [g5, f5]) pre3 ?_ rh
      rw [hflat, ← hpc3, h1]
      cases dest <;> simp [isLabelHOL, Flapjack.Compiler.Backend.StackToLab.compileJumpHOL] <;> omega
    · obtain ⟨ys, m2, fetchJ, locH, instYs, locEnd, total, -⟩ := callHandlerCode h1 inst0
      cases r with
      | some x =>
        exact callComposeSome budget (by omega) run13 (by rw [g1, f1]) (by rw [g2, f2])
          (by rw [g3, f3]) (by rw [g4, f4]) (by rw [g5, f5]) pre3 rh
      | none =>
        obtain ⟨ck2, continuationBound, t4, run4, k1, k2, k3, k4, k5, pre4, hpc4, rel4⟩ := rh
        rw [h1] at hpc4
        have pre34 := pre3.trans pre4
        have fetchJ4 : asmFetchAux t4.pc t4.code =
            some (.labAsm (.jump (.lab n m2)) 0 [] 0) := by
          rw [hpc4, ← hpc3]; exact asmFetchAuxSomeIsPrefix _ _ _ _ ⟨fetchJ, pre34⟩
        have locEnd4 := locToPcIsPrefix _ _ _ _ _ ⟨locEnd, pre34⟩
        refine ⟨(1 + ck') + ck2 + 1, by omega, { t4 with pc := t1.pc + 1 + 1 +
            ((appListAppend xs).filter (fun x => !isLabelHOL x)).length + 1 +
            ((appListAppend ys).filter (fun x => !isLabelHOL x)).length }, fun ck1 => ?_,
          by rw [k1, g1, f1], by rw [k2, g2, f2], by rw [k3, g3, f3], by rw [k4, g4, f4],
          by rw [k5, g5, f5], pre34, ?_, rel4⟩
        · rw [show t1.clock + ((1 + ck') + ck2 + 1) + ck1 =
              t1.clock + ((1 + ck') + ck2) + (ck1 + 1) by omega, chainRun run13 run4,
            show t4.clock + (ck1 + 1) = (t4.clock + ck1) + 1 by omega,
            jumpStep (t4.clock + ck1) fetchJ4 locEnd4]
        · simp only [total]; omega
  · -- the callee raised
    rcases handler with _ | ⟨hp, hs, hl⟩
    · simp only at ev'
      simp only [Prod.mk.injEq] at ev'
      obtain ⟨rfl, rfl⟩ := ev'
      exact prop _ (fun _ _ _ _ _ _ => by cases v <;> rfl) ph
    · simp only at ev'
      by_cases hv : v = .loc hs hl
      swap; · rw [if_pos hv] at ev'; exact (err ev').elim
      rw [if_neg (not_not.mpr hv)] at ev'
      subst hv
      obtain ⟨ys, m2, -, locH, instYs, -, total, h2⟩ := callHandlerCode h1 inst0
      obtain ⟨ck', calleeBound, t3, run3, g1, g2, g3, g4, g5, pre3, hw⟩ :=
        boundedFlattenConclVloc (n1 := hs) (n2 := hl) budget rfl rfl ph
      rw [fcode] at pre3
      obtain ⟨hpc3, rel3⟩ := hw _ (locToPcIsPrefix _ _ _ _ _ ⟨locH, pre3⟩)
      simp only at caH
      have lt3 : MeasureLt hp s2' (.call (some (rp, link, l1, l2)) dest (some (hp, hs, hl))) s1 :=
        .inl hs2clk
      have rh := ih hp s2' lt3 false r s2 n m1 cs bs t3
        ⟨ev', nerr, rel3, by rw [g1, g2, g3, g4, g5, f1, f2, f3, f4, f5]; exact caH,
          by rw [← hpc3, h2]; exact codeInstalledIsPrefix _ _ _ _ ⟨instYs, pre3⟩,
          fun k hk => isSomeLocToPcPrefix ⟨labs k hk, pre3⟩⟩
      have handlerLe : pathWork hp s2' ≤ budget := by
        dsimp only [budget]
        omega
      have rh := boundedFlattenConcl_mono handlerLe rh
      refine callCompose budget (by omega) (chainRun run1 run3) (by rw [g1, f1]) (by rw [g2, f2])
        (by rw [g3, f3]) (by rw [g4, f4]) (by rw [g5, f5]) pre3 ?_ rh
      rw [total, ← hpc3, h2]
      omega
  · exact (err ev').elim
  · exact (err ev').elim
  all_goals
    simp only [Prod.mk.injEq] at ev'
    obtain ⟨rfl, rfl⟩ := ev'
    exact prop _ (fun _ _ _ _ _ _ => rfl) ph

end
end InitECandidate.Runtime.StackToLab
#print axioms InitECandidate.Runtime.StackToLab.pathWork_tailCall_bound

#print axioms InitECandidate.Runtime.StackToLab.pathWork_returnCall_bound
