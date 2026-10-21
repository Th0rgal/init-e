import InitECandidate.Runtime.SourceCostSharpCrepBasis
import InitECandidate.Runtime.CrepWorkF
import InitECandidate.Runtime.PanSourcePriceState
namespace InitECandidate.Runtime.FineCost
open Flapjack Flapjack.Pancake.PanLang

/-! A price model for the source-to-Crep transfer at function-indexed Crep work.
Compiled Crep expressions are priced by `pr` (a list by the sum), statements at
`S`, calls at `callP` per (caller, callee, return count) and a stopped call at
`shortP`. The model fields are exactly the inequalities between these Crep
prices and the source event weights that the transfer uses; of the expression
price the transfer uses only the source domination of compiled expressions and
bounds on the compiler-introduced variable, constant, global-read and
variable-plus-offset nodes. -/

/-- Price of the stores of `n` words from an address of price `a`: the first
word stores at the address, each further word at the address plus an offset
(surcharge `O`); each stored word is a variable (price `V`). -/
def storeWordsCost (S : StmtK) (V O a n : Nat) : Nat :=
  n * (S.store + a + O + V) - O * (n - (n - 1))

structure SharpModel where
  pr : CrepExpHOL 64 → Nat
  /-- Bounds on the compiler-introduced nodes: a variable, a constant, and a
  variable plus a constant offset (surcharge `O`). -/
  V : Nat
  C : Nat
  O : Nat
  S : StmtK
  callP : CName → CName → Nat → Nat
  shortP : Nat
  varOk : ∀ n, pr (.var n) ≤ V
  cstOk : ∀ w, pr (.const w) ≤ C
  globOk : ∀ a, pr (.loadGlob a) ≤ V
  offOk : ∀ n w, pr (.op .add [.var n, .const w]) ≤ V + O
  /-- Source expression events pay the compiled expressions' prices. -/
  exprOk : ∀ {F : Type} (s : PanSemStateFiniteExact 64 F) (context : PanToCrepContextExact 64)
    (targetLocals : HolFiniteMapExact Nat (HolWordLab 64)),
    panToCrepLocalsRelFiniteExact context s.locals targetLocals →
    ∀ (expression : ExpHOL 64) (value : ValueHOL 64), expressionValue s expression = some value →
      localisedExpHOL expression = true →
      ((compileExpExactHOLW context expression).1.map pr).sum ≤ sharpScore (expressionEvents s expression)
  /-- A moved word (`copy` event) pays a variable read. -/
  copyOk : V ≤ 24
  /-- Zero-initialised return slots pay their constants. -/
  slotOk : ∀ n, n * C ≤ slotOverhead n
  breakOk : S.brk ≤ statementUnit
  contOk : S.cont ≤ statementUnit
  tickOk : S.tick ≤ statementUnit
  iteOk : S.ite ≤ statementUnit
  whileOk : S.wh ≤ whileOverhead
  returnOk : ∀ n, S.ret n ≤ returnOverhead n
  /-- Raising `n` words: a global store of each temporary, then the raise. -/
  raiseOk : ∀ n, n * (S.storeGlob + V) + S.raise ≤ raiseOverhead n
  /-- Storing `n` words through a variable address. -/
  storeOk : ∀ n, storeWordsCost S V O V n ≤ storeOverhead n
  store32Ok : S.store32 ≤ storeOverhead 1
  /-- An external call pays within its fixed statement charge. -/
  ffiOk : S.ffi ≤ externalOverhead
  /-- A shared-memory access pays within its native event. -/
  shMemOk : S.shMem ≤ 37
  /-- The source primitive (three argument words, a two-word result): its
  overhead and the copy of the result words. -/
  primOk : S.prim 2 3 ≤ primitiveOverhead 3 + 24 * 2
  /-- A call's price and argument passing are within the call overhead and the
  certified call-site surcharge of its (caller, callee). -/
  callOk : ∀ fn g n a, n ≤ 21 → callP fn g n + S.argP a ≤ callOverhead a + callSites fn g
  /-- Returned words and an exception exit are within the caller's exit charge. -/
  retWOk : ∀ n, S.retW * n ≤ returnCopy n
  exnOk : ∀ n, S.exnP ≤ returnCopy n + 147
  /-- A caught exception: copying its `n` payload words from globals into the
  handler variable, and the handler dispatch. -/
  handlerOk : ∀ n, n * V + S.hdlP ≤ returnCopy n + 147

/-- A model's price of an expression list: the sum. -/
def SharpModel.prs (M : SharpModel) (es : List (CrepExpHOL 64)) : Nat := (es.map M.pr).sum

/-- Crep work at a model's prices. -/
abbrev CrepWorkM (M : SharpModel) {σ : Type} :=
  @CrepWorkF M.pr M.prs M.S M.callP M.shortP σ

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
    M.prs (compileExpExactHOLW context expression).1 ≤ sharpScore (expressionEvents s expression) :=
  M.exprOk s context targetLocals related expression value evaluated localised

theorem prs_nil : M.prs [] = 0 := rfl

theorem prs_cons (e : CrepExpHOL 64) (es : List (CrepExpHOL 64)) : M.prs (e :: es) = M.pr e + M.prs es := by
  simp [prs]

theorem prs_append (l r : List (CrepExpHOL 64)) : M.prs (l ++ r) = M.prs l + M.prs r := by
  simp [prs, List.sum_append]

theorem prs_head (head : CrepExpHOL 64) (tail : List (CrepExpHOL 64)) : M.pr head ≤ M.prs (head :: tail) := by
  rw [prs_cons]; omega

theorem prs_variables (names : List Nat) : M.prs (names.map (CrepExpHOL.var (width := 64))) ≤ names.length * M.V := by
  induction names with
  | nil => simp [prs]
  | cons name names ih =>
    have := M.varOk name
    rw [List.map_cons, prs_cons, List.length_cons, Nat.succ_mul]; omega

theorem prs_consts (n : Nat) (w : BitVec 64) : M.prs (List.replicate n (CrepExpHOL.const w)) ≤ n * M.C := by
  induction n with
  | zero => simp [prs]
  | succ n ih =>
    have := M.cstOk w
    rw [List.replicate_succ, prs_cons, Nat.succ_mul]; omega

end SharpModel

#print axioms SharpModel.expression_paid
end InitECandidate.Runtime.FineCost
