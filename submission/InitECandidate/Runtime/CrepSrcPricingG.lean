import InitECandidate.Runtime.CrepTightPricingG
import InitECandidate.Runtime.PanSourcePrice
namespace InitECandidate.Runtime.FineCost
open Flapjack

/-! The pattern-aware selector Loop pricing at the source charge's Crep
expression prices `nodePriceK srcK`: the source pays exactly these prices,
and they dominate the selector prices and hence `nodeT`. -/

/-- A Loop pricing at pointwise larger Crep expression prices. -/
def LoopPricingG.weaken (P : LoopPricingG) (price' : CrepExpHOL 64 → Nat)
    (priceList' : List (CrepExpHOL 64) → Nat) (hp : ∀ e, P.price e ≤ price' e)
    (hl : ∀ es, P.priceList es ≤ priceList' es) : LoopPricingG :=
  { P with
    price := price'
    priceList := priceList'
    exprOk := fun context tmp live e => by
      obtain ⟨cost, h, b⟩ := P.exprOk context tmp live e
      exact ⟨cost, h, Nat.le_trans b (hp e)⟩
    listOk := fun context tmp live es => by
      obtain ⟨cost, h, b⟩ := P.listOk context tmp live es
      exact ⟨cost, h, Nat.le_trans b (hl es)⟩ }

mutual
  theorem selNodePrice_selK : ∀ e : CrepExpHOL 64, selNodePrice e = nodePriceK selK e
    | .const _ | .var _ | .loadGlob _ | .baseAddr | .topAddr => by simp [selNodePrice, nodePriceK]
    | .load a | .load32 a | .loadByte a => by simp [selNodePrice, nodePriceK, selNodePrice_selK a]
    | .op _ args | .crepOp _ args => by
      simp [selNodePrice, nodePriceK, selPriceList_selK args, Nat.add_assoc]
    | .shift _ l r | .cmp _ l r => by simp [selNodePrice, nodePriceK, selNodePrice_selK l, selNodePrice_selK r]
  termination_by e => sizeOf e
  decreasing_by all_goals first | sizeOf_list_dec | decreasing_trivial

  theorem selPriceList_selK : ∀ es : List (CrepExpHOL 64), selPriceList es = nodePriceListK selK es
    | [] => by simp [selPriceList, nodePriceListK]
    | e :: es => by simp [selPriceList, nodePriceListK, selNodePrice_selK e, selPriceList_selK es]
  termination_by es => sizeOf es
  decreasing_by all_goals first | sizeOf_list_dec | decreasing_trivial
end

/-- Source-charge price of an argument list, with the per-value move. -/
def srcPriceListM (es : List (CrepExpHOL 64)) : Nat := nodePriceListK srcK es + 39 * es.length

theorem nodeT_le_srcK (c : Compiler.Encoders.Asm.AsmConfigExact 64) (e : CrepExpHOL 64) :
    nodeT c e ≤ nodePriceK srcK e := by
  have h1 := nodeT_le_sel c e
  rw [selNodePrice_selK] at h1
  exact Nat.le_trans h1 (nodePriceK_mono selK_le_srcK e)

theorem nodeTs_le_srcK (c : Compiler.Encoders.Asm.AsmConfigExact 64) :
    ∀ es : List (CrepExpHOL 64), nodeTs c es ≤ nodePriceListK srcK es
  | [] => by simp [nodeTs, nodePriceListK]
  | e :: es => by
    have := nodeT_le_srcK c e; have := nodeTs_le_srcK c es
    rw [nodeTs_cons]; simp only [nodePriceListK]; omega

noncomputable def srcPricing (c : Compiler.Encoders.Asm.AsmConfigExact 64) : LoopPricingG :=
  (tightPricing c).weaken (nodePriceK srcK) srcPriceListM
    (fun e => nodeT_le_srcK c e)
    (fun es => by
      show nodeTsM c es ≤ _
      have := nodeTs_le_srcK c es
      simp only [nodeTsM, srcPriceListM]; omega)

theorem srcPricing_fit (c : Compiler.Encoders.Asm.AsmConfigExact 64) {unit prim ret shortP : Nat}
    {callP : CName → CName → Nat → Nat} {funcs : HolFiniteMapExact Basis.Pure.MlString.MlString (Nat × Nat)}
    (hu : 37 ≤ unit) (hffi : ffiSel ≤ unit) (hp : 111 ≤ prim) (hr : 49 ≤ ret)
    (callOk : ∀ fn g n, (wsLeaf c).call + (wsLeaf c).cont + (wsLeaf c).cs (labOf funcs fn) (labOf funcs g) + (wsLeaf c).ts (labOf funcs g) +
      (wsLeaf c).rn n + (wsLeaf c).rn 1 ≤ callP fn g n)
    (shortOk : (wsLeaf c).shortC ≤ shortP) :
    CrepFitG (srcPricing c) unit prim ret shortP callP funcs :=
  let f := tightPricing_fit c (funcs := funcs) hu hffi hp hr callOk shortOk
  { f with }

/-- Crep work at the source charge's prices transfers to function-indexed Loop
work at the actual compiled leaf prices `wsLeaf c`. -/
theorem crep_loop_src_workG (c : Compiler.Encoders.Asm.AsmConfigExact 64) {unit prim ret shortP : Nat}
    {callP : CName → CName → Nat → Nat} {funcs : HolFiniteMapExact Basis.Pure.MlString.MlString (Nat × Nat)}
    (fit : CrepFitG (srcPricing c) unit prim ret shortP callP funcs) {F : Type} {fn : CName}
    {t : CrepSemHOLState 64 F} {p : CrepProgHOL 64} {w : Nat}
    (work : @CrepWorkF (nodePriceK srcK) srcPriceListM unit prim callP shortP ret F fn t p w)
    (u : LoopSemStateFiniteExact 64 F) (context : CrepToLoopContextExact) (live : NumSet)
    (hfun : context.funcs = funcs) (ok : (evalCrepSemHOLProgExact t p).1 ≠ some .error)
    (rel : CrepLoopRel context live t u) :
    LoopPaidG (wsLeaf c) (labOf funcs fn) context live t u p w :=
  crep_loop_executed_workG (srcPricing c) fit work u context live hfun ok rel

#print axioms selNodePrice_selK
#print axioms srcPricing
#print axioms srcPricing_fit
#print axioms crep_loop_src_workG
end InitECandidate.Runtime.FineCost
