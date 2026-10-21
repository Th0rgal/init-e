import InitECandidate.Runtime.CrepSharpInstance
import InitECandidate.Runtime.PanSourcePriceT
namespace InitECandidate.Runtime.FineCost
open Flapjack Flapjack.Pancake.PanLang Flapjack.LoopSemStateFiniteExact Flapjack.Pancake.CrepToLoop.Proofs.NCompileCorrect

/-! The concrete price model at the pattern-aware expression price `tightP c`
(the selector price with operand folding, closed under `simp_exp`). Its source
domination holds against today's `srcK` charge (`tightP ≤ selNodePrice ≤ srcK`)
and, exactly, against the mirror charge `sourcePriceT` (`sourcePriceT_compile`). -/

theorem tightP_le_sel (c : Compiler.Encoders.Asm.AsmConfigExact 64) (e : CrepExpHOL 64) :
    tightP c e ≤ selNodePrice e := by
  unfold tightP
  have h1 := nodeT_le_sel c e
  have h2 := nodeT_le_sel c (crepSimpExpHOL e)
  have h3 := nodePriceK_simp (K := selK) (by decide) e
  rw [← selNodePrice_selK, ← selNodePrice_selK] at h3
  omega

theorem immC_le (c : Compiler.Encoders.Asm.AsmConfigExact 64) (o : BinOp) (w : BitVec 64) : immC c o w ≤ 48 := by
  unfold immC; split <;> omega

theorem tightP_var (c : Compiler.Encoders.Asm.AsmConfigExact 64) (n : Nat) : tightP c (.var n) = 24 := by
  unfold tightP
  rw [show crepSimpExpHOL (.var n : CrepExpHOL 64) = .var n by simp [crepSimpExpHOL], nodeT.eq_2]; rfl

theorem tightP_const (c : Compiler.Encoders.Asm.AsmConfigExact 64) (w : BitVec 64) : tightP c (.const w) = 24 := by
  unfold tightP
  rw [show crepSimpExpHOL (.const w : CrepExpHOL 64) = .const w by simp [crepSimpExpHOL], nodeT.eq_1]; rfl

theorem tightP_loadGlob (c : Compiler.Encoders.Asm.AsmConfigExact 64) (a : BitVec 5) :
    tightP c (.loadGlob a) = 24 := by
  unfold tightP
  rw [show crepSimpExpHOL (.loadGlob a : CrepExpHOL 64) = .loadGlob a by simp [crepSimpExpHOL], nodeT.eq_3]; rfl

theorem tightP_offset (c : Compiler.Encoders.Asm.AsmConfigExact 64) (n : Nat) (w : BitVec 64) :
    tightP c (.op .add [.var n, .const w]) ≤ 24 + 48 := by
  unfold tightP
  have hs : crepSimpExpHOL (.op .add [.var n, .const w] : CrepExpHOL 64) = .op .add [.var n, .const w] := by
    simp [crepSimpExpHOL]
  rw [hs, Nat.max_self, nodeT.eq_15 c .add (.var n) w (by decide)]
  have := immC_le c .add w
  simp only [safeC, if_true]
  rw [nodeT.eq_2]
  omega

/-- The concrete model at the pattern-aware expression price. -/
noncomputable def tightModel (c : Compiler.Encoders.Asm.AsmConfigExact 64)
    (funcs : HolFiniteMapExact Basis.Pure.MlString.MlString (Nat × Nat))
    (aligned : CallSitesAligned c funcs) : SharpModel :=
  { selModel c funcs aligned with
    pr := tightP c
    varOk := fun n => (tightP_var c n).le
    cstOk := fun w => (tightP_const c w).le
    globOk := fun a => (tightP_loadGlob c a).le
    offOk := fun n w => tightP_offset c n w
    exprOk := fun s context targetLocals related e v evaluated localised => by
      have le : ((compileExpExactHOLW context e).1.map (tightP c)).sum ≤
          ((compileExpExactHOLW context e).1.map (nodePriceK selK)).sum := by
        apply List.sum_le_sum
        intro x _
        rw [← selNodePrice_selK]; exact tightP_le_sel c x
      refine Nat.le_trans le ?_
      rw [← nodePriceListK_eq_sum, sharpScore_expressionEvents]
      exact sourcePrice_compile_le selK_le_srcK s context targetLocals related e v evaluated localised }

theorem tightModel_fit (c : Compiler.Encoders.Asm.AsmConfigExact 64)
    (funcs : HolFiniteMapExact Basis.Pure.MlString.MlString (Nat × Nat))
    (aligned : CallSitesAligned c funcs) : (tightModel c funcs aligned).LoopFit c funcs where
  nodeOk := fun e => nodeT_le_tightP c e
  simpOk := fun e => tightP_simp c e
  stmtOk := StmtK.Le.refl' (selK_min c)
  callOk := fun _ _ _ => Nat.le_refl _
  shortOk := Nat.le_refl _

/-- End-to-end statement transfer at the pattern-aware model. -/
theorem source_loop_tight_work {F : Type} (c : Compiler.Encoders.Asm.AsmConfigExact 64)
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
      wl ≤ sharpScore events + (tightModel c funcs aligned).stopP r ∧
      LoopRunRel loopContext live
        (evalCrepSemHOLProgExact (crepSimpMapcsHOL t) (crepSimpProgHOL (compileProgExactHOLW context p)))
        (evaluate (compileHOLExact loopContext live (crepSimpProgHOL (compileProgExactHOLW context p)))
          { u with clock := u.clock + extra }) ∧
      (evaluate (compileHOLExact loopContext live (crepSimpProgHOL (compileProgExactHOLW context p)))
          { u with clock := u.clock + extra }).1 ≠ some .error :=
  (tightModel c funcs aligned).source_loop_work c (tightModel_fit c funcs aligned) run t context resultOk rel
    localised checked codeChecked small fsmall width codeWidth u loopContext live hfun loopRel

#print axioms tightModel
#print axioms source_loop_tight_work
end InitECandidate.Runtime.FineCost
