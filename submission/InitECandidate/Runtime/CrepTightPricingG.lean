import InitECandidate.Runtime.CrepSelTight
import InitECandidate.Runtime.CrepSelPricingG
namespace InitECandidate.Runtime.FineCost
open Flapjack

/-! The pattern-aware selector pricing in the generic transfer: Crep work at
`nodeT` prices becomes function-indexed Loop work at the actual compiled leaf
prices `wsLeaf c`. -/

theorem tightPricing_fit (c : Compiler.Encoders.Asm.AsmConfigExact 64) {K : StmtK} {shortP : Nat}
    {callP : CName → CName → Nat → Nat} {funcs : HolFiniteMapExact Basis.Pure.MlString.MlString (Nat × Nat)}
    (hK : StmtK.Le (selK_min c) K)
    (callOk : ∀ fn g n, (wsLeaf c).call + (wsLeaf c).cont + (wsLeaf c).cs (labOf funcs fn) (labOf funcs g) + (wsLeaf c).ts (labOf funcs g) +
      (wsLeaf c).rn n + (wsLeaf c).rn 1 ≤ callP fn g n)
    (shortOk : (wsLeaf c).shortC ≤ shortP) :
    CrepFitG (tightPricing c) K shortP callP funcs where
  tickOk := hK.tick
  breakOk := hK.brk
  contOk := hK.cont
  ffiOk := hK.ffi
  raiseOk := hK.raise
  setOk := hK.storeGlob
  shareOk := hK.shMem
  storeOk := hK.store
  store32Ok := hK.store32
  returnOk := hK.ret
  primOk := hK.prim
  iteOk := hK.ite
  whileBreakOk := hK.wh
  whileContOk := Nat.le_trans (by show 14 + 29 + 0 ≤ 14 + 29 + 2; omega) hK.wh
  argOk := hK.argP
  retOk := hK.retW
  exnOk := hK.exnP
  handleOk := hK.hdlP
  callOk := callOk
  shortOk := shortOk

/-- Crep work at the pattern-aware selector prices transfers to function-indexed
Loop work at the actual compiled leaf prices `wsLeaf c`. -/
theorem crep_loop_tight_workG (c : Compiler.Encoders.Asm.AsmConfigExact 64) {K : StmtK} {shortP : Nat}
    {callP : CName → CName → Nat → Nat} {funcs : HolFiniteMapExact Basis.Pure.MlString.MlString (Nat × Nat)}
    (fit : CrepFitG (tightPricing c) K shortP callP funcs) {F : Type} {fn : CName}
    {t : CrepSemHOLState 64 F} {p : CrepProgHOL 64} {w : Nat}
    (work : @CrepWorkF (nodeT c) (nodeTsM c) K callP shortP F fn t p w)
    (u : LoopSemStateFiniteExact 64 F) (context : CrepToLoopContextExact) (live : NumSet)
    (hfun : context.funcs = funcs) (ok : (evalCrepSemHOLProgExact t p).1 ≠ some .error)
    (rel : CrepLoopRel context live t u) :
    LoopPaidG (wsLeaf c) (labOf funcs fn) context live t u p w :=
  crep_loop_executed_workG (tightPricing c) fit work u context live hfun ok rel

#print axioms tightPricing_fit
#print axioms crep_loop_tight_workG
end InitECandidate.Runtime.FineCost
