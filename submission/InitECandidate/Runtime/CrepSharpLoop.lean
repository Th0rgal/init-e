import InitECandidate.Runtime.CrepSharpControl
import InitECandidate.Runtime.CrepWorkFSimp
import InitECandidate.Runtime.CrepSrcPricingG
namespace InitECandidate.Runtime.FineCost
open Flapjack Flapjack.Pancake.PanLang Flapjack.LoopSemStateFiniteExact Flapjack.Pancake.CrepToLoop.Proofs.NCompileCorrect

/-! End-to-end statement transfer at a price model: source → pan_to_crep →
simp_prog → crep_to_loop (with the installed optimiser), into function-indexed
Loop work at the actual compiled leaf prices `wsLeaf c`. The model's
expression price must dominate the pattern-aware selector price `nodeT` and
its statement prices the least prices the selector chain needs
(`selK_min c ≤ S`). -/

/-- The pattern-aware selector Loop pricing at Crep expression prices `pr ≥ nodeT`. -/
noncomputable def modelPricing (c : Compiler.Encoders.Asm.AsmConfigExact 64) (pr : CrepExpHOL 64 → Nat)
    (hp : ∀ e, nodeT c e ≤ pr e) : LoopPricingG :=
  (tightPricing c).weaken pr (fun es => (es.map pr).sum) hp (fun es => by
    show nodeTs c es ≤ (es.map pr).sum
    induction es with
    | nil => simp [nodeTs]
    | cons e es ih => rw [nodeTs_cons]; have := hp e; simp only [List.map_cons, List.sum_cons]; omega)

/-- How a price model meets the compiled code: its expression price dominates
the pattern-aware selector price and `simp_exp` never increases it,
statement prices dominate the selector chain's least prices, and call and
stopped-call prices pay the compiled call sequence at the callers' and
callees' Loop labels in `funcs`. -/
structure SharpModel.LoopFit (M : SharpModel) (c : Compiler.Encoders.Asm.AsmConfigExact 64)
    (funcs : HolFiniteMapExact Basis.Pure.MlString.MlString (Nat × Nat)) : Prop where
  nodeOk : ∀ e, nodeT c e ≤ M.pr e
  simpOk : ∀ e, M.pr (crepSimpExpHOL e) ≤ M.pr e
  stmtOk : StmtK.Le (selK_min c) M.S
  callOk : ∀ fn g n, (wsLeaf c).call + (wsLeaf c).cont + (wsLeaf c).cs (labOf funcs fn) (labOf funcs g) +
    (wsLeaf c).ts (labOf funcs g) + (wsLeaf c).rn n + (wsLeaf c).rn 1 ≤ M.callP fn g n
  shortOk : (wsLeaf c).shortC ≤ M.shortP

/-- The pinned Pan-to-Crep result relation never relates a non-error source
result to a Crep `Error` (as `resultRel_not_error`, outside the old Loop chain). -/
theorem resultRel_ne_error {F : Type} {context : PanToCrepContextExact 64}
    {post : PanSemStateFiniteExact 64 F} {t1 : CrepSemHOLState 64 F}
    {r : Option (PanSemResultExact 64)} {r1 : Option (CrepResultHOLExact 64)}
    (rel : pcCompileCorrectResultRel context post t1 r r1) : r1 ≠ some .error := by
  intro h
  subst h
  rcases r with _ | r
  · simp [pcCompileCorrectResultRel] at rel
  · cases r with
    | exception eid v =>
      simp only [pcCompileCorrectResultRel] at rel
      split at rel
      · exact rel
      · simp at rel
    | _ => simp [pcCompileCorrectResultRel] at rel

namespace SharpModel
variable (M : SharpModel) {fn : Flapjack.Pancake.PanLang.MlS}

theorem LoopFit.fit {M : SharpModel} {c : Compiler.Encoders.Asm.AsmConfigExact 64}
    {funcs : HolFiniteMapExact Basis.Pure.MlString.MlString (Nat × Nat)} (h : M.LoopFit c funcs) :
    CrepFitG (modelPricing c M.pr h.nodeOk) M.S M.shortP M.callP funcs :=
  let f := tightPricing_fit c (funcs := funcs) h.stmtOk h.callOk h.shortOk
  { f with }

/-- Model end-to-end statement transfer: the compiled Loop run in the source
function's label does at most the source trace's score, plus the once-paid
stopped-call charge on a timed-out trace, of work at the actual compiled leaf
prices `wsLeaf c`. -/
theorem source_loop_work {F : Type} (c : Compiler.Encoders.Asm.AsmConfigExact 64)
    {funcs : HolFiniteMapExact Basis.Pure.MlString.MlString (Nat × Nat)} (fit : M.LoopFit c funcs)
    {s post : PanSemStateFiniteExact 64 F}
    {p : ProgHOL 64} {r : Option (PanSemResultExact 64)} {events : List WorkEvent}
    (run : StatementRun fn s p r post events) (t : CrepSemHOLState 64 F)
    (context : PanToCrepContextExact 64) (resultOk : r ≠ some .error)
    (rel : SourceCrepRel context s t) (localised : localisedProgHOL p = true)
    (checked : sharpSitesProg sharpReplayBound p = true)
    (codeChecked : ∀ function shapes body returnShape,
      s.code.lookup function = some (shapes, body, returnShape) →
        sharpSitesProg sharpReplayBound body = true)
    (small : VarsSmall context) (fsmall : FuncsSmall context) (width : widthProg p = true)
    (codeWidth : CodeWidth s.code)
    (u : LoopSemStateFiniteExact 64 F) (loopContext : CrepToLoopContextExact) (live : NumSet)
    (hfun : loopContext.funcs = funcs)
    (loopRel : CrepLoopRel loopContext live (crepSimpMapcsHOL t) u) :
    ∃ extra wl,
      LoopWorkG (wsLeaf c) (labOf funcs fn) { u with clock := u.clock + extra }
        (compileHOLExact loopContext live (crepSimpProgHOL (compileProgExactHOLW context p)))
        (evaluate (compileHOLExact loopContext live (crepSimpProgHOL (compileProgExactHOLW context p)))
          { u with clock := u.clock + extra }) wl ∧
      wl ≤ sharpScore events + M.stopP r ∧
      LoopRunRel loopContext live
        (evalCrepSemHOLProgExact (crepSimpMapcsHOL t) (crepSimpProgHOL (compileProgExactHOLW context p)))
        (evaluate (compileHOLExact loopContext live (crepSimpProgHOL (compileProgExactHOLW context p)))
          { u with clock := u.clock + extra }) ∧
      (evaluate (compileHOLExact loopContext live (crepSimpProgHOL (compileProgExactHOLW context p)))
          { u with clock := u.clock + extra }).1 ≠ some .error := by
  obtain ⟨w, crepWork, crepBound⟩ := M.source_crep_executed_work run t context resultOk rel
    localised checked codeChecked small fsmall width codeWidth
  obtain ⟨r1, t1, crepRun, _, _, _, resultRel⟩ := compiled_source_run t context run.sound
    resultOk rel.state rel.code rel.exceptions rel.locals localised
  have ok : (evalCrepSemHOLProgExact t (compileProgExactHOLW context p)).1 ≠ some .error := by
    rw [crepRun]; exact resultRel_ne_error resultRel
  obtain ⟨ws, simpWork, simpBound⟩ := CrepWorkF.simp fit.simpOk (fun es => by
    show ((es.map crepSimpExpHOL).map M.pr).sum ≤ (es.map M.pr).sum
    induction es with
    | nil => simp
    | cons e es ih => have := fit.simpOk e; simp only [List.map_cons, List.sum_cons]; omega) crepWork ok
  have simpOk : (evalCrepSemHOLProgExact (crepSimpMapcsHOL t)
      (crepSimpProgHOL (compileProgExactHOLW context p))).1 ≠ some .error := by
    rw [crepArithSimpProgCorrect _ t r1 t1 crepRun (resultRel_ne_error resultRel)]
    exact resultRel_ne_error resultRel
  obtain ⟨extra, wl, work, bound, runRel⟩ :=
    crep_loop_executed_workG (modelPricing c M.pr fit.nodeOk) fit.fit simpWork u loopContext live
      hfun simpOk loopRel
  refine ⟨extra, wl, work, by omega, runRel, ?_⟩
  rw [runRel.2.2.2.2.1]
  revert simpOk
  generalize (evalCrepSemHOLProgExact (crepSimpMapcsHOL t) (crepSimpProgHOL (compileProgExactHOLW context p))).1 = cr
  intro h
  rcases cr with _ | (_ | _ | _ | _ | _ | _ | _) <;> simp_all [resultToLoop]

end SharpModel

#print axioms SharpModel.source_loop_work
end InitECandidate.Runtime.FineCost
