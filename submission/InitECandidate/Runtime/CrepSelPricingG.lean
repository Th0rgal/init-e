import InitECandidate.Runtime.CrepLoopControlG
import InitECandidate.Runtime.CrepWorkFMono
import InitECandidate.Runtime.CrepSelPrice
namespace InitECandidate.Runtime.FineCost
open Flapjack

/-! The selector-derived Loop pricing as a `LoopPricingG`: leaves at
`wsLeaf c`, expression code at the selector allowance, Crep expressions at
`selNodePrice`. The generic transfer then gives Crep-to-indexed-Loop work at
the actual compiled leaf prices. -/

theorem fLs_cons (v : HolLoopExp 64) (vs : List (HolLoopExp 64)) : fLs (v :: vs) = fL v + fLs vs := by
  simp [fLs]

/-- Selector price of an argument list, with the per-value move. -/
def selPriceListM (es : List (CrepExpHOL 64)) : Nat := selPriceList es + 39 * es.length

noncomputable def selPricing (c : Compiler.Encoders.Asm.AsmConfigExact 64) : LoopPricingG where
  L := wsLeaf c
  A := selAllowance c
  vp := fL
  vps := fLs
  vps_nil := by simp [fLs]
  vps_cons := fLs_cons
  price := selNodePrice
  priceList := selPriceListM
  exprOk := fun context tmp live e => by
    obtain ⟨cost, h, b⟩ := crep_to_loop_sel_work context tmp live e
    exact ⟨cost, by rw [selAllowance_works]; exact h, b⟩
  listOk := fun context tmp live es => by
    obtain ⟨cost, h, b⟩ := crep_to_loop_sel_list_work context tmp live es
    have len := sel_compileExps_length context es tmp live
    refine ⟨cost, by rw [selAllowance_works]; exact h, ?_⟩
    simp only [selPriceListM]
    omega
  assignWork := fun n v => ⟨fL v, by simp [selAllowance, selCodeWork], Nat.le_refl _⟩
  assignOk := fun n v => leafPL_assign c wsT1 wsT2 n v
  tickC := 6
  tickOk := ⟨6, (leafPL_simple c).2.1, Nat.le_refl _⟩
  breakC := 2
  breakOk := fun l => ⟨2, (leafPL_simple c).2.2.1 l, Nat.le_refl _⟩
  contC := 0
  contOk := fun l => ⟨0, (leafPL_simple c).2.2.2.1 l, Nat.le_refl _⟩
  constC := 24
  constOk := fun w => by simp [fL]
  raiseC := 63
  raiseOk := fun e => ⟨63, (leafPL_simple c).2.2.2.2.1 e, Nat.le_refl _⟩
  returnC := 15
  returnOk := fun vs => ⟨15, (leafPL_simple c).2.2.2.2.2.1 vs, Nat.le_refl _⟩
  setC := 12
  setOk := fun a v => leafPL_setGlobal c wsT1 wsT2 a v
  shareC := 13
  shareOk := fun op n v => leafPL_shMem c wsT1 wsT2 op n v
  storeC := 24
  storeOk := fun e v => leafPL_store c wsT1 wsT2 e v
  store32C := 24
  store32Ok := fun a v => ⟨24, (leafPL_simple c).2.2.2.2.2.2.1 a v, Nat.le_refl _⟩
  storeByteOk := fun a v => ⟨24, (leafPL_simple c).2.2.2.2.2.2.2 a v, Nat.le_refl _⟩
  ffiC := ffiSel
  ffiOk := fun f a b d e live => ⟨ffiSel, leafPL_ffi c f a b d e live, Nat.le_refl _⟩
  primC := 111
  primOk := fun ds op as => leafPL_primitive c ds op as

/-- The least statement prices the selector-derived Loop prices need. -/
def selK_min (_c : Compiler.Encoders.Asm.AsmConfigExact 64) : StmtK where
  tick := 6
  brk := 2
  cont := 0
  ffi := ffiSel
  raise := 24 + 63
  storeGlob := 12
  shMem := 13
  store := 24
  store32 := 24
  ret := fun _ => 15
  prim := fun _ _ => 111
  ite := 29
  wh := 14 + 29 + 2
  argP := fun n => 39 * (n + 1 - 22)
  retW := 0
  exnP := 29 + 63
  hdlP := 29 + 6

/-- The selector pricing's fit, from its numeric conditions and the
per-(caller, callee, return count) call price. -/
theorem selPricing_fit (c : Compiler.Encoders.Asm.AsmConfigExact 64) {K : StmtK} {shortP : Nat}
    {callP : CName → CName → Nat → Nat} {funcs : HolFiniteMapExact Basis.Pure.MlString.MlString (Nat × Nat)}
    (hK : StmtK.Le (selK_min c) K)
    (callOk : ∀ fn g n, (wsLeaf c).call + (wsLeaf c).cont + (wsLeaf c).cs (labOf funcs fn) (labOf funcs g) + (wsLeaf c).ts (labOf funcs g) +
      (wsLeaf c).rn n + (wsLeaf c).rn 1 ≤ callP fn g n)
    (shortOk : (wsLeaf c).shortC ≤ shortP) :
    CrepFitG (selPricing c) K shortP callP funcs where
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

/-- Crep work at selector prices transfers to function-indexed Loop work at the
actual compiled leaf prices `wsLeaf c`. -/
theorem crep_loop_sel_workG (c : Compiler.Encoders.Asm.AsmConfigExact 64) {K : StmtK} {shortP : Nat}
    {callP : CName → CName → Nat → Nat} {funcs : HolFiniteMapExact Basis.Pure.MlString.MlString (Nat × Nat)}
    (fit : CrepFitG (selPricing c) K shortP callP funcs) {F : Type} {fn : CName}
    {t : CrepSemHOLState 64 F} {p : CrepProgHOL 64} {w : Nat}
    (work : @CrepWorkF selNodePrice selPriceListM K callP shortP F fn t p w)
    (u : LoopSemStateFiniteExact 64 F) (context : CrepToLoopContextExact) (live : NumSet)
    (hfun : context.funcs = funcs) (ok : (evalCrepSemHOLProgExact t p).1 ≠ some .error)
    (rel : CrepLoopRel context live t u) :
    LoopPaidG (wsLeaf c) (labOf funcs fn) context live t u p w :=
  crep_loop_executed_workG (selPricing c) fit work u context live hfun ok rel

#print axioms selPricing
#print axioms selPricing_fit
#print axioms crep_loop_sel_workG
end InitECandidate.Runtime.FineCost
