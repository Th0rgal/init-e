import InitECandidate.Runtime.PanSourcePrice
import InitECandidate.Runtime.PanReadPresence
import Flapjack.Pancake.Proofs.PanToCrep.StateRelFiniteSupport
namespace InitECandidate.Runtime.FineCost
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact

/-- Under the `pan_to_crep` locals relation, a present local carries the same
price information in the source state and in the compiler context. -/
theorem valueInfo_context {F : Type} {s : PanSemStateFiniteExact 64 F}
    {context : PanToCrepContextExact 64} {targetLocals : HolFiniteMapExact Nat (HolWordLab 64)}
    (related : panToCrepLocalsRelFiniteExact context s.locals targetLocals)
    {name : MlStringHOL} {value : ValueHOL 64} (present : s.locals.lookup name = some value) :
    valueInfo s.locals name = contextInfo context name := by
  obtain ⟨slots, found, width, -⟩ :=
    panToCrepLocalsRelLookupCtxtFiniteExact context s.locals targetLocals name value related present
  simp [valueInfo, contextInfo, present, found, width]

/-- The source price of a localised expression whose reads are present is the
`srcK` price of the Crep words `pan_to_crep` emits for it. -/
theorem sourcePrices_compile {F : Type} (s : PanSemStateFiniteExact 64 F)
    (context : PanToCrepContextExact 64) (targetLocals : HolFiniteMapExact Nat (HolWordLab 64))
    (related : panToCrepLocalsRelFiniteExact context s.locals targetLocals)
    (e : ExpHOL 64) (localised : localisedExpHOL e = true)
    (present : ∀ name, name ∈ varExpHOL e → ∃ value, s.locals.lookup name = some value) :
    sourcePrices s e =
      ((compileExpExactHOLW context e).1.map (nodePriceK srcK), (compileExpExactHOLW context e).2) := by
  rw [sourcePrices, exprPrices_localised _ _ _ (fun _ => none) e localised,
    exprPrices_congr_local _ _ (contextInfo context) _ e (fun name member => by
      obtain ⟨value, found⟩ := present name member
      exact valueInfo_context related found),
    exprPrices_compile]

/-- The executed form: a successfully evaluated localised expression costs
exactly its source price after `pan_to_crep`, at `srcK`. -/
theorem sourcePrice_compileK {F : Type} (s : PanSemStateFiniteExact 64 F)
    (context : PanToCrepContextExact 64) (targetLocals : HolFiniteMapExact Nat (HolWordLab 64))
    (related : panToCrepLocalsRelFiniteExact context s.locals targetLocals)
    (e : ExpHOL 64) (value : ValueHOL 64) (evaluated : expressionValue s e = some value)
    (localised : localisedExpHOL e = true) :
    nodePriceListK srcK (compileExpExactHOLW context e).1 = sourcePrice s e := by
  have prices := sourcePrices_compile s context targetLocals related e localised
    (expression_success_locals_present s e value evaluated)
  rw [sourcePrice, prices, nodePriceListK_eq_sum]

/-- Any node cost below `srcK` prices the compiled words within the source price. -/
theorem sourcePrice_compile_le {F : Type} {K : NodeK} (le : NodeK.Le K srcK) (s : PanSemStateFiniteExact 64 F)
    (context : PanToCrepContextExact 64) (targetLocals : HolFiniteMapExact Nat (HolWordLab 64))
    (related : panToCrepLocalsRelFiniteExact context s.locals targetLocals)
    (e : ExpHOL 64) (value : ValueHOL 64) (evaluated : expressionValue s e = some value)
    (localised : localisedExpHOL e = true) :
    nodePriceListK K (compileExpExactHOLW context e).1 ≤ sourcePrice s e := by
  rw [← sourcePrice_compileK s context targetLocals related e value evaluated localised]
  exact nodePriceListK_mono le _

/-- The default-Loop price of the compiled words is within the source price. -/
theorem sourcePrice_compile {F : Type} (s : PanSemStateFiniteExact 64 F)
    (context : PanToCrepContextExact 64) (targetLocals : HolFiniteMapExact Nat (HolWordLab 64))
    (related : panToCrepLocalsRelFiniteExact context s.locals targetLocals)
    (e : ExpHOL 64) (value : ValueHOL 64) (evaluated : expressionValue s e = some value)
    (localised : localisedExpHOL e = true) :
    loopPriceList (compileExpExactHOLW context e).1 ≤ sourcePrice s e := by
  rw [← nodePriceListK_loopK]
  exact sourcePrice_compile_le loopK_le_srcK s context targetLocals related e value evaluated localised

#print axioms sourcePrices_compile
#print axioms sourcePrice_compile
#print axioms sourcePrice_compileK
#print axioms sourcePrice_compile_le
end InitECandidate.Runtime.FineCost
