import InitECandidate.Runtime.SourceCostSharpCrepBasis
import InitECandidate.Runtime.CrepWorkF
namespace InitECandidate.Runtime.FineCost
open Flapjack Flapjack.Pancake.PanLang

/-! A price model for the source-to-Crep transfer at function-indexed Crep work.
Compiled Crep expressions are priced structurally at node costs `K`
(`nodePriceK K`), statements at `S`, calls at `callP` per (caller, callee,
return count) and a stopped call at `shortP`. The model fields are exactly the
inequalities between these Crep prices and the source event weights that the
transfer uses. -/

/-- Price of the stores of `n` words from an address of price `a`: the first
word stores at the address, each further word at an added constant offset;
each stored word is a variable. -/
def storeWordsCost (K : NodeK) (S : StmtK) (a n : Nat) : Nat :=
  n * (S.store + a + K.cst + K.op 2 + K.var) - (K.cst + K.op 2) * (n - (n - 1))

structure SharpModel where
  K : NodeK
  S : StmtK
  callP : CName → CName → Nat → Nat
  shortP : Nat
  /-- Source expression events pay the compiled expressions' prices. -/
  exprLe : NodeK.Le K srcK
  /-- A moved word (`copy` event) pays a variable read. -/
  copyOk : K.var ≤ 14
  /-- Zero-initialised return slots pay their constants. -/
  slotOk : ∀ n, n * K.cst ≤ slotOverhead n
  breakOk : S.brk ≤ statementUnit
  contOk : S.cont ≤ statementUnit
  tickOk : S.tick ≤ statementUnit
  iteOk : S.ite ≤ statementUnit
  whileOk : S.wh ≤ whileOverhead
  returnOk : ∀ n, S.ret n ≤ returnOverhead n
  /-- Raising `n` words: a global store of each temporary, then the raise. -/
  raiseOk : ∀ n, n * (S.storeGlob + K.var) + S.raise ≤ raiseOverhead n
  /-- Storing `n` words through a variable address. -/
  storeOk : ∀ n, storeWordsCost K S K.var n ≤ storeOverhead n
  store32Ok : S.store32 ≤ storeOverhead 1
  primOk : ∀ a b, S.prim a b ≤ primitiveOverhead (a + b)
  /-- A call's price and argument passing are within the call overhead and the
  certified call-site surcharge of its (caller, callee). -/
  callOk : ∀ fn g n a, callP fn g n + S.argP a ≤ callOverhead a + callSites fn g
  /-- Returned words and an exception exit are within the caller's exit charge. -/
  retWOk : ∀ n, S.retW * n ≤ returnCopy n
  exnOk : ∀ n, S.exnP ≤ returnCopy n + 147
  /-- A caught exception: copying its `n` payload words from globals into the
  handler variable, and the handler dispatch. -/
  handlerOk : ∀ n, n * K.var + S.hdlP ≤ returnCopy n + 147

/-- Crep work at a model's prices. -/
abbrev CrepWorkM (M : SharpModel) {σ : Type} :=
  @CrepWorkF (nodePriceK M.K) (nodePriceListK M.K) M.S M.callP M.shortP σ

/-- A uniform priced-work ceiling for a non-recursive Crep fragment, in every function. -/
def CrepBoundedM (M : SharpModel) (program : CrepProgHOL 64) (bound : Nat) : Prop :=
  ∀ (σ : Type) (fn : CName) (t : CrepSemHOLState 64 σ), ∃ w, CrepWorkM M fn t program w ∧ w ≤ bound

namespace SharpModel
variable (M : SharpModel)

theorem bounded_mono {program : CrepProgHOL 64} {small large : Nat}
    (bounded : CrepBoundedM M program small) (le : small ≤ large) : CrepBoundedM M program large := by
  intro σ fn t
  obtain ⟨w, work, bound⟩ := bounded σ fn t
  exact ⟨w, work, by omega⟩

/-- Source expression events pay the compiled expressions at the model's prices. -/
theorem expression_paid {F : Type} (s : PanSemStateFiniteExact 64 F)
    (context : PanToCrepContextExact 64)
    (targetLocals : HolFiniteMapExact Nat (HolWordLab 64))
    (related : panToCrepLocalsRelFiniteExact context s.locals targetLocals)
    (expression : ExpHOL 64) (value : ValueHOL 64)
    (evaluated : expressionValue s expression = some value)
    (localised : localisedExpHOL expression = true) :
    nodePriceListK M.K (compileExpExactHOLW context expression).1 ≤ sharpScore (expressionEvents s expression) := by
  rw [sharpScore_expressionEvents]
  exact sourcePrice_compile_le M.exprLe s context targetLocals related expression value evaluated localised

end SharpModel

#print axioms SharpModel.expression_paid
end InitECandidate.Runtime.FineCost
