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
native Loop price of the Crep words `pan_to_crep` emits for it. -/
theorem sourcePrices_compile {F : Type} (s : PanSemStateFiniteExact 64 F)
    (context : PanToCrepContextExact 64) (targetLocals : HolFiniteMapExact Nat (HolWordLab 64))
    (related : panToCrepLocalsRelFiniteExact context s.locals targetLocals)
    (e : ExpHOL 64) (localised : localisedExpHOL e = true)
    (present : ∀ name, name ∈ varExpHOL e → ∃ value, s.locals.lookup name = some value) :
    sourcePrices s e =
      ((compileExpExactHOLW context e).1.map loopNodePrice, (compileExpExactHOLW context e).2) := by
  rw [sourcePrices, exprPrices_localised _ _ (fun _ => none) e localised,
    exprPrices_congr_local _ (contextInfo context) _ e (fun name member => by
      obtain ⟨value, found⟩ := present name member
      exact valueInfo_context related found),
    exprPrices_compile]

/-- The executed form: a successfully evaluated localised expression costs
exactly its source price after `pan_to_crep`. -/
theorem sourcePrice_compile {F : Type} (s : PanSemStateFiniteExact 64 F)
    (context : PanToCrepContextExact 64) (targetLocals : HolFiniteMapExact Nat (HolWordLab 64))
    (related : panToCrepLocalsRelFiniteExact context s.locals targetLocals)
    (e : ExpHOL 64) (value : ValueHOL 64) (evaluated : expressionValue s e = some value)
    (localised : localisedExpHOL e = true) :
    loopPriceList (compileExpExactHOLW context e).1 = sourcePrice s e := by
  have prices := sourcePrices_compile s context targetLocals related e localised
    (expression_success_locals_present s e value evaluated)
  rw [sourcePrice, prices, loopPriceList_eq_sum]

#print axioms sourcePrices_compile
#print axioms sourcePrice_compile
end InitECandidate.Runtime.FineCost
