import InitECandidate.Runtime.CrepLoopIfG
import InitECandidate.Runtime.CrepLoopDecG
import InitECandidate.Runtime.CrepLoopWhileG
import InitECandidate.Runtime.CrepLoopCallG
namespace InitECandidate.Runtime.FineCost
open Flapjack Flapjack.LoopSemStateFiniteExact Flapjack.Pancake.CrepToLoop.Proofs.NCompileCorrect

/-- Crep-to-Loop executed-work transfer at a generic Loop pricing, by
induction on function-indexed Crep work. Crep function `fn` runs as Loop
function `labOf funcs fn` (its `crep_to_loop` label); calls charge their
(caller, callee) Loop surcharges through `CrepFitG.callOk`. Unconditional:
the optimisation pass is root's `loop_optimise_executed_workG`. -/
theorem crep_loop_executed_workG (P : LoopPricingG) {unit prim ret shortP : Nat}
    {callP : CName → CName → Nat → Nat} {funcs : HolFiniteMapExact Basis.Pure.MlString.MlString (Nat × Nat)}
    (fit : CrepFitG P unit prim ret shortP callP funcs) {F : Type} {fn : CName}
    {t : CrepSemHOLState 64 F} {p : CrepProgHOL 64} {w : Nat}
    (work : CrepWorkG P unit prim callP shortP ret fn t p w) :
    ∀ (u : LoopSemStateFiniteExact 64 F) (context : CrepToLoopContextExact) (live : NumSet),
      context.funcs = funcs →
      (evalCrepSemHOLProgExact t p).1 ≠ some .error → CrepLoopRel context live t u →
      LoopPaidG P.L (labOf funcs fn) context live t u p w := by
  induction work with
  | @seqNext fn t first second middle firstWork secondWork one run two ihOne ihTwo =>
    intro u context live hfun ok rel
    have okSeq := ok
    rw [evalCrepSemHOLProgExact_seq_holShape, run] at okSeq
    simp only [if_true] at okSeq
    obtain ⟨e1, w1, work1, bound1, rel1⟩ := ihOne u context live hfun (by rw [run]; simp) rel
    rw [run] at rel1
    obtain ⟨norm1, mid⟩ := rels_of_run rel1 rfl
    rcases hrun1 : evaluate (compileHOLExact context live first)
        { u with clock := u.clock + e1 } with ⟨r1, u1⟩
    rw [hrun1] at work1 norm1 mid
    simp only at norm1 mid
    subst norm1
    obtain ⟨e2, w2, work2, bound2, rel2⟩ := ihTwo u1 context live hfun okSeq mid
    have lifted := LoopWorkG.add_clock work1 e2 (by simp)
    simp only [] at lifted
    have combined := LoopWorkG.seqNext lifted work2
    have state : ({ u with clock := u.clock + (e1 + e2) } : LoopSemStateFiniteExact 64 F) =
        { ({ u with clock := u.clock + e1 } : LoopSemStateFiniteExact 64 F) with
          clock := u.clock + e1 + e2 } := by
      simp [Nat.add_assoc]
    refine ⟨e1 + e2, w1 + w2, ?_, by omega, ?_⟩
    · rw [state]
      have sound := LoopWorkG.sound combined
      simp only [compileHOLExact] at sound ⊢
      rw [sound]
      exact combined
    · have sound := LoopWorkG.sound combined
      rw [state]
      simp only [compileHOLExact] at sound ⊢
      rw [sound, evalCrepSemHOLProgExact_seq_holShape, run]
      simp only [if_true]
      exact rel2
  | @seqStop fn t first second result middle firstWork one run ihOne =>
    intro u context live hfun ok rel
    obtain ⟨e1, w1, work1, bound1, rel1⟩ := ihOne u context live hfun (by
      have okSeq := ok
      rw [evalCrepSemHOLProgExact_seq_holShape, run] at okSeq
      rw [run]; simpa using okSeq) rel
    rw [run] at rel1
    rcases hrun1 : evaluate (compileHOLExact context live first)
        { u with clock := u.clock + e1 } with ⟨r1, u1⟩
    rw [hrun1] at work1 rel1
    have notNone : r1 ≠ none := by
      obtain ⟨_, _, _, _, hr, _⟩ := rel1
      simp only at hr
      rw [hr]
      cases result <;> simp [resultToLoop]
    obtain ⟨r1', rfl⟩ := Option.ne_none_iff_exists'.mp notNone
    have combined := LoopWorkG.seqStop (second := compileHOLExact context live second) work1
    refine ⟨e1, w1, ?_, by omega, ?_⟩
    · have sound := LoopWorkG.sound combined
      simp only [compileHOLExact] at sound ⊢
      rw [sound]
      exact combined
    · have sound := LoopWorkG.sound combined
      simp only [compileHOLExact] at sound ⊢
      rw [sound, evalCrepSemHOLProgExact_seq_holShape, run]
      simp only [reduceCtorEq, if_false]
      exact rel1
  | @iteBranch fn t condition yes no word branchWork guard branch ihBranch =>
    intro u context live hfun ok rel
    have okBranch : (evalCrepSemHOLProgExact t (if word ≠ 0 then yes else no)).1 ≠ some .error := by
      rw [evalCrepSemHOLProgExact_ite_holShape, guard] at ok; exact ok
    exact ite_loop_paidG P (labOf funcs fn) fit.iteOk guard ok rel (fun u' rel' => ihBranch u' context live hfun okBranch rel')
  | @iteInvalid fn t condition yes no invalid =>
    intro u context live hfun ok rel
    exfalso
    apply ok
    rw [evalCrepSemHOLProgExact_ite_holShape]
    split
    · rename_i w hw; exact absurd hw (invalid w)
    · rfl
  | @dec fn t name value body word bodyWork evaluated bodyRun ih =>
    intro u context live hfun ok rel
    exact dec_loop_paidG P (labOf funcs fn) evaluated ok rel (fun u' c' l' hf ok' rel' => ih u' c' l' (hf.trans hfun) ok' rel')
  | @decFailure fn t name value body failed =>
    intro u context live hfun ok rel
    exfalso
    apply ok
    rw [evalCrepSemHOLProgExact_dec_holShape, failed]
  | @whileExit fn t condition body exit =>
    intro u context live hfun ok rel
    cases hev : evalCrepSemHOLExp t condition with
    | none =>
      exfalso; apply ok; rw [evalCrepSemHOLProgExact_while_holShape, hev]
    | some v =>
      cases v with
      | word w =>
        have hw := exit w hev
        subst hw
        exact while_false_loop_paidG P (labOf funcs fn) fit.iteOk fit.iterOk fit.breakOk fit.contOk hev rel
  | @whileTimeout fn t condition body word guard nonzero clock =>
    intro u context live hfun ok rel
    exact while_timeout_loop_paidG P (labOf funcs fn) fit.iteOk fit.iterOk fit.breakOk fit.contOk guard nonzero clock rel
  | @whileLoop fn t condition body word bodyWork result middle restWork guard nonzero clock one run
      again rest ihOne ihRest =>
    intro u context live hfun ok rel
    have bodyOk := while_body_not_error guard nonzero clock run ok
    have restOk : (evalCrepSemHOLProgExact middle (.while condition body)).1 ≠ some .error := by
      have crepRun : evalCrepSemHOLProgExact t (.while condition body) =
          evalCrepSemHOLProgExact middle (.while condition body) := by
        rw [evalCrepSemHOLProgExact_while_holShape, guard]
        simp only [ne_eq, clock, if_false]
        rw [if_pos nonzero, run]
        rcases again with rfl | rfl <;> rfl
      rw [← crepRun]; exact ok
    exact while_loop_loop_paidG P (labOf funcs fn) fit.iteOk fit.iterOk fit.breakOk fit.contOk guard nonzero clock run again rel
      (fun u' rel' => ihOne u' context live hfun (by rw [run]; exact bodyOk) rel')
      (fun u' rel' => ihRest u' context live hfun restOk rel')
  | @whileStop fn t condition body word bodyWork result middle guard nonzero clock one run stop
      ihOne =>
    intro u context live hfun ok rel
    have bodyOk := while_body_not_error guard nonzero clock run ok
    exact while_stop_loop_paidG P (labOf funcs fn) fit.iteOk fit.iterOk fit.breakOk fit.contOk guard nonzero clock run stop ok rel
      (fun u' rel' => ihOne u' context live hfun (by rw [run]; exact bodyOk) rel')
  | @callShort fn t returnInfo function arguments short =>
    intro u context live hfun ok rel
    refine call_loop_paidG P fit fn returnInfo function arguments t u context hfun live _ ok rel
      (fun _ => Nat.le_refl _) ?_
    intro args prog newlocals hargs hlookup hnames hclock
    exfalso
    rcases short with hnone | ⟨values, hvals, hrest⟩
    · rw [hnone] at hargs; cases hargs
    · rw [hvals] at hargs; cases hargs
      rcases hrest with hl | hn | hc
      · rw [hl] at hlookup; cases hlookup
      · cases returnInfo with
        | none => exact hn
        | some info => exact hnames hn
      · exact hclock hc
  | @callBody fn t returnInfo function arguments values body locals bodyWork result post args lookup
      names clock bodyRun run unhandled ihBody =>
    intro u context live hfun ok rel
    refine call_loop_paidG P fit fn returnInfo function arguments t u context hfun live _ ok rel
      (fun h => absurd h clock) ?_
    intro args' prog newlocals hargs hlookup _ _
    rw [args] at hargs; cases hargs
    rw [lookup] at hlookup; cases hlookup
    refine ⟨bodyWork, fun u' c' l' hf ok' rel' => ihBody u' c' l' hf ok' rel', ?_, ?_⟩
    · intro r final hrun _
      rw [run] at hrun; cases hrun
      exact Nat.le_refl _
    · intro st eid rts hp hrun hcal
      rw [run] at hrun; cases hrun
      exact absurd hcal (unhandled eid rts hp rfl)
  | @callHandler fn t rts code handler function arguments values body locals bodyWork post
      handlerWork args lookup names clock bodyRun run handlerRun ihBody ihHandler =>
    intro u context live hfun ok rel
    refine call_loop_paidG P fit fn _ function arguments t u context hfun live _ ok rel
      (fun h => absurd h clock) ?_
    intro args' prog newlocals hargs hlookup _ _
    rw [args] at hargs; cases hargs
    rw [lookup] at hlookup; cases hlookup
    refine ⟨bodyWork, fun u' c' l' hf ok' rel' => ihBody u' c' l' hf ok' rel', ?_, ?_⟩
    · intro r final hrun hun
      rw [run] at hrun; cases hrun
      exact absurd rfl (hun code rts handler rfl)
    · intro st eid rts' hp hrun hcal
      rw [run] at hrun; cases hrun
      cases hcal
      exact ⟨handlerWork, fun u' ok' rel' => ihHandler u' context live hfun ok' rel', Nat.le_refl _⟩
  | _ =>
    intro u context live hfun ok rel
    exact leaf_loop_paidG P fit _ rfl ok rel

#print axioms crep_loop_executed_workG
end InitECandidate.Runtime.FineCost
