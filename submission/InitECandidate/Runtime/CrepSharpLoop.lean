import InitECandidate.Runtime.CrepSharpControl
import InitECandidate.Runtime.CrepWorkFSimp
import InitECandidate.Runtime.CrepSrcPricingG
namespace InitECandidate.Runtime.FineCost
open Flapjack Flapjack.Pancake.PanLang Flapjack.LoopSemStateFiniteExact Flapjack.Pancake.CrepToLoop.Proofs.NCompileCorrect

/-! End-to-end statement transfer at a price model: source → pan_to_crep →
simp_prog → crep_to_loop (with the installed optimiser), into function-indexed
Loop work at the actual compiled leaf prices `wsLeaf c`. The model's node
costs must dominate the selector's (`selK ≤ K`) and its statement prices the
least prices the selector chain needs (`selK_min c ≤ S`). -/

theorem nodeT_le_K (c : Compiler.Encoders.Asm.AsmConfigExact 64) {K : NodeK} (hK : NodeK.Le selK K)
    (e : CrepExpHOL 64) : nodeT c e ≤ nodePriceK K e := by
  have h1 := nodeT_le_sel c e
  rw [selNodePrice_selK] at h1
  exact Nat.le_trans h1 (nodePriceK_mono hK e)

theorem nodeTs_le_K (c : Compiler.Encoders.Asm.AsmConfigExact 64) {K : NodeK} (hK : NodeK.Le selK K) :
    ∀ es : List (CrepExpHOL 64), nodeTs c es ≤ nodePriceListK K es
  | [] => by simp [nodeTs, nodePriceListK]
  | e :: es => by
    have := nodeT_le_K c hK e; have := nodeTs_le_K c hK es
    rw [nodeTs_cons]; simp only [nodePriceListK]; omega

/-- The pattern-aware selector Loop pricing at node-cost prices `K ≥ selK`. -/
noncomputable def modelPricing (c : Compiler.Encoders.Asm.AsmConfigExact 64) (K : NodeK)
    (hK : NodeK.Le selK K) : LoopPricingG :=
  (tightPricing c).weaken (nodePriceK K) (nodePriceListK K) (nodeT_le_K c hK) (nodeTs_le_K c hK)

/-- How a price model meets the compiled code: node costs dominate the
selector's, a shift is no dearer than a multiplication (for `simp_prog`),
statement prices dominate the selector chain's least prices, and call and
stopped-call prices pay the compiled call sequence at the callers' and
callees' Loop labels in `funcs`. -/
structure SharpModel.LoopFit (M : SharpModel) (c : Compiler.Encoders.Asm.AsmConfigExact 64)
    (funcs : HolFiniteMapExact Basis.Pure.MlString.MlString (Nat × Nat)) : Prop where
  nodeOk : NodeK.Le selK M.K
  simpOk : M.K.shift ≤ M.K.crepOp
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
    CrepFitG (modelPricing c M.K h.nodeOk) M.S M.shortP M.callP funcs :=
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
    localised checked codeChecked
  obtain ⟨r1, t1, crepRun, _, _, _, resultRel⟩ := compiled_source_run t context run.sound
    resultOk rel.state rel.code rel.exceptions rel.locals localised
  have ok : (evalCrepSemHOLProgExact t (compileProgExactHOLW context p)).1 ≠ some .error := by
    rw [crepRun]; exact resultRel_ne_error resultRel
  obtain ⟨ws, simpWork, simpBound⟩ := CrepWorkF.simp (nodePriceK_simp fit.simpOk)
    (nodePriceListK_simp fit.simpOk) crepWork ok
  have simpOk : (evalCrepSemHOLProgExact (crepSimpMapcsHOL t)
      (crepSimpProgHOL (compileProgExactHOLW context p))).1 ≠ some .error := by
    rw [crepArithSimpProgCorrect _ t r1 t1 crepRun (resultRel_ne_error resultRel)]
    exact resultRel_ne_error resultRel
  obtain ⟨extra, wl, work, bound, runRel⟩ :=
    crep_loop_executed_workG (modelPricing c M.K fit.nodeOk) fit.fit simpWork u loopContext live
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
