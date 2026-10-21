import InitECandidate.Runtime.CrepSharpLoop
namespace InitECandidate.Runtime.FineCost
open Flapjack Flapjack.Pancake.PanLang Flapjack.LoopSemStateFiniteExact Flapjack.Pancake.CrepToLoop.Proofs.NCompileCorrect

/-! The concrete price model: selector node costs (`selK`), the selector
chain's least statement prices (`selK_min c`), and call prices equal to the
compiled Loop call sequence at the callers' and callees' labels in `funcs`.
The one premise is call-site alignment: the Loop call-site and tail surcharges
at the `funcs` labels are within the source call-site charge. -/

theorem ffiSel_eq : ffiSel = 121 := by decide +kernel

theorem NodeK.Le.refl' (K : NodeK) : NodeK.Le K K :=
  ⟨Nat.le_refl _, Nat.le_refl _, Nat.le_refl _, Nat.le_refl _, Nat.le_refl _, fun _ => Nat.le_refl _,
    Nat.le_refl _, Nat.le_refl _, Nat.le_refl _⟩

theorem StmtK.Le.refl' (S : StmtK) : StmtK.Le S S :=
  ⟨Nat.le_refl _, Nat.le_refl _, Nat.le_refl _, Nat.le_refl _, Nat.le_refl _, Nat.le_refl _,
    Nat.le_refl _, Nat.le_refl _, Nat.le_refl _, fun _ => Nat.le_refl _, fun _ _ => Nat.le_refl _,
    Nat.le_refl _, Nat.le_refl _, fun _ => Nat.le_refl _, Nat.le_refl _, Nat.le_refl _, Nat.le_refl _⟩

/-- The compiled Loop call sequence of a call from `fn` to `g` naming `n` return slots. -/
noncomputable def selCallP (c : Compiler.Encoders.Asm.AsmConfigExact 64)
    (funcs : HolFiniteMapExact Basis.Pure.MlString.MlString (Nat × Nat)) (fn g : CName) (n : Nat) : Nat :=
  (wsLeaf c).call + (wsLeaf c).cont + (wsLeaf c).cs (labOf funcs fn) (labOf funcs g) +
    (wsLeaf c).ts (labOf funcs g) + (wsLeaf c).rn n + (wsLeaf c).rn 1

/-- Call-site alignment of a Loop function table with the source call charge. -/
def CallSitesAligned (c : Compiler.Encoders.Asm.AsmConfigExact 64)
    (funcs : HolFiniteMapExact Basis.Pure.MlString.MlString (Nat × Nat)) : Prop :=
  ∀ fn g, (wsLeaf c).cs (labOf funcs fn) (labOf funcs g) + (wsLeaf c).ts (labOf funcs g) ≤ callSites fn g

/-- The concrete price model. -/
noncomputable def selModel (c : Compiler.Encoders.Asm.AsmConfigExact 64)
    (funcs : HolFiniteMapExact Basis.Pure.MlString.MlString (Nat × Nat))
    (aligned : CallSitesAligned c funcs) : SharpModel where
  pr := nodePriceK selK
  V := 24
  C := 24
  O := 48
  S := selK_min c
  callP := selCallP c funcs
  shortP := (wsLeaf c).shortC
  varOk := fun _ => by simp [nodePriceK]
  cstOk := fun _ => by simp [nodePriceK]
  globOk := fun _ => by simp [nodePriceK]
  offOk := fun _ _ => by simp [nodePriceK, nodePriceListK]
  exprOk := fun s context targetLocals related e v evaluated localised => by
    rw [← nodePriceListK_eq_sum, sharpScore_expressionEvents]
    exact sourcePrice_compile_le selK_le_srcK s context targetLocals related e v evaluated localised
  copyOk := by decide
  slotOk := fun n => by simp [slotOverhead]; omega
  breakOk := by simp [selK_min, statementUnit]
  contOk := by simp [selK_min, statementUnit]
  tickOk := by simp [selK_min, statementUnit]
  iteOk := by simp [selK_min, statementUnit]
  whileOk := by simp [selK_min, whileOverhead, statementUnit]
  returnOk := fun n => by simp [selK_min, returnOverhead, statementUnit]; omega
  raiseOk := fun n => by simp [selK_min, raiseOverhead]; omega
  storeOk := fun n => by simp [storeWordsCost, selK_min, storeOverhead]; omega
  store32Ok := by simp [selK_min, storeOverhead]
  ffiOk := by simp [selK_min, ffiSel_eq, externalOverhead]
  shMemOk := by simp [selK_min]
  primOk := by simp [selK_min, primitiveOverhead]
  callOk := fun fn g n a hn => by
    have h := aligned fn g
    simp only [selCallP, selK_min, callOverhead] at h ⊢
    simp only [wsLeaf] at h ⊢
    omega
  retWOk := fun n => by simp [selK_min, returnCopy]
  exnOk := fun n => by simp [selK_min]
  handlerOk := fun n => by simp [selK_min, returnCopy]; omega

theorem selModel_fit (c : Compiler.Encoders.Asm.AsmConfigExact 64)
    (funcs : HolFiniteMapExact Basis.Pure.MlString.MlString (Nat × Nat))
    (aligned : CallSitesAligned c funcs) : (selModel c funcs aligned).LoopFit c funcs where
  nodeOk := fun e => by
    show nodeT c e ≤ nodePriceK selK e
    rw [← selNodePrice_selK]; exact nodeT_le_sel c e
  simpOk := fun e => nodePriceK_simp (K := selK) (by decide) e
  stmtOk := StmtK.Le.refl' (selK_min c)
  callOk := fun _ _ _ => Nat.le_refl _
  shortOk := Nat.le_refl _

/-- End-to-end statement transfer at the concrete model: under call-site
alignment and the width premises, the compiled Loop run does at most the
source trace's score, plus the stopped-call charge once on a timed-out trace,
of work at the actual compiled leaf prices `wsLeaf c`. -/
theorem source_loop_sel_work {F : Type} (c : Compiler.Encoders.Asm.AsmConfigExact 64)
    {funcs : HolFiniteMapExact Basis.Pure.MlString.MlString (Nat × Nat)}
    (aligned : CallSitesAligned c funcs) {fn : MlS}
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
      wl ≤ sharpScore events + (selModel c funcs aligned).stopP r ∧
      LoopRunRel loopContext live
        (evalCrepSemHOLProgExact (crepSimpMapcsHOL t) (crepSimpProgHOL (compileProgExactHOLW context p)))
        (evaluate (compileHOLExact loopContext live (crepSimpProgHOL (compileProgExactHOLW context p)))
          { u with clock := u.clock + extra }) ∧
      (evaluate (compileHOLExact loopContext live (crepSimpProgHOL (compileProgExactHOLW context p)))
          { u with clock := u.clock + extra }).1 ≠ some .error :=
  (selModel c funcs aligned).source_loop_work c (selModel_fit c funcs aligned) run t context resultOk rel
    localised checked codeChecked small fsmall width codeWidth u loopContext live hfun loopRel

#print axioms ffiSel_eq
#print axioms selModel
#print axioms source_loop_sel_work
end InitECandidate.Runtime.FineCost
