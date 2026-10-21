import InitECandidate.Runtime.CrepSelTight
import InitECandidate.Runtime.CrepSelPricingG
namespace InitECandidate.Runtime.FineCost
open Flapjack

/-! The pattern-aware selector pricing in the generic transfer: Crep work at
`nodeT` prices becomes function-indexed Loop work at the actual compiled leaf
prices `wsLeaf c`. -/

theorem tightPricing_fit (c : Compiler.Encoders.Asm.AsmConfigExact 64) {unit prim ret shortP : Nat}
    {callP : CName → CName → Nat → Nat} {funcs : HolFiniteMapExact Basis.Pure.MlString.MlString (Nat × Nat)}
    (hu : 37 ≤ unit) (hffi : ffiSel ≤ unit) (hp : 111 ≤ prim) (hr : 49 ≤ ret)
    (callOk : ∀ fn g n, 196 + (wsLeaf c).cs (labOf funcs fn) (labOf funcs g) + (wsLeaf c).ts (labOf funcs g) +
      (wsLeaf c).rn n + (wsLeaf c).rn 1 ≤ callP fn g n)
    (shortOk : (wsLeaf c).shortC ≤ shortP) :
    CrepFitG (tightPricing c) unit prim ret shortP callP funcs where
  unitOk := hu
  retOk := hr
  tickOk := by show 6 ≤ unit; omega
  breakOk := by show 2 ≤ unit; omega
  contOk := by show 0 ≤ unit; omega
  ffiOk := hffi
  raiseOk := by show 24 + 63 ≤ prim + 1; omega
  setOk := by show 12 ≤ unit; omega
  shareOk := by show 13 ≤ unit; omega
  storeOk := by show 24 ≤ unit; omega
  store32Ok := by show 24 ≤ unit; omega
  returnOk := by show 15 ≤ unit; omega
  primOk := hp
  handleOk := by show 37 + 6 ≤ ret; omega
  raiseRetOk := by show 37 + 63 ≤ 3 * ret; omega
  callOk := callOk
  shortOk := shortOk

/-- Crep work at the pattern-aware selector prices transfers to function-indexed
Loop work at the actual compiled leaf prices `wsLeaf c`. -/
theorem crep_loop_tight_workG (c : Compiler.Encoders.Asm.AsmConfigExact 64) {unit prim ret shortP : Nat}
    {callP : CName → CName → Nat → Nat} {funcs : HolFiniteMapExact Basis.Pure.MlString.MlString (Nat × Nat)}
    (fit : CrepFitG (tightPricing c) unit prim ret shortP callP funcs) {F : Type} {fn : CName}
    {t : CrepSemHOLState 64 F} {p : CrepProgHOL 64} {w : Nat}
    (work : @CrepWorkF (nodeT c) (nodeTsM c) unit prim callP shortP ret F fn t p w)
    (u : LoopSemStateFiniteExact 64 F) (context : CrepToLoopContextExact) (live : NumSet)
    (hfun : context.funcs = funcs) (ok : (evalCrepSemHOLProgExact t p).1 ≠ some .error)
    (rel : CrepLoopRel context live t u) :
    LoopPaidG (wsLeaf c) (labOf funcs fn) context live t u p w :=
  crep_loop_executed_workG (tightPricing c) fit work u context live hfun ok rel

#print axioms tightPricing_fit
#print axioms crep_loop_tight_workG
end InitECandidate.Runtime.FineCost
