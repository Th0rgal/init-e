import InitECandidate.Runtime.SourceCostGlobalsRun
namespace InitECandidate.Runtime.FineCost
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact

/-! The one-time initialiser cost of `pan_globals`'s generated entry: each
global initialised by a constant becomes one `TopAddr` store. -/

/-- Every global declaration is initialised by a constant. -/
def constGlobalDecls : List (DeclHOL 64) → Bool
  | [] => true
  | .decl _ _ (.const _) :: rest => constGlobalDecls rest
  | .decl _ _ _ :: _ => false
  | _ :: rest => constGlobalDecls rest

/-- A constant store to a `TopAddr` slot. -/
def ConstStores (inits : List (ProgHOL 64)) : Prop :=
  ∀ i ∈ inits, ∃ address word, i = .store (.op .sub [.topAddr, .const address]) (.const word)

theorem globals_constStores : ∀ (decls : List (DeclHOL 64)) (context : PanGlobalsContextExact 64),
    constGlobalDecls decls = true → ConstStores (compileDecsExactHOL context decls).1
  | [], _, _ => by simp [compileDecsExactHOL, ConstStores]
  | .decl shape name value :: rest, context, ready => by
    cases value with
    | const word =>
      simp only [constGlobalDecls] at ready
      intro i hi
      simp only [compileDecsExactHOL] at hi
      rcases List.mem_cons.1 hi with rfl | hi
      · refine ⟨context.globalsSize + cakeBytesInWord 64 * BitVec.ofNat 64 (sizeOfShapeHOL shape), word, ?_⟩
        rw [compileDecsGlobalAddressExact_eq]
        simp [compileExpExactHOL]
      · exact globals_constStores rest _ ready i hi
    | _ => simp [constGlobalDecls] at ready
  | .function declaration :: rest, context, ready => by
    simp only [constGlobalDecls] at ready
    intro i hi
    simp only [compileDecsExactHOL] at hi
    exact globals_constStores rest context ready i hi
  | .exnDecl name shape :: rest, context, ready => by
    simp only [constGlobalDecls] at ready
    intro i hi
    simp only [compileDecsExactHOL] at hi
    exact globals_constStores rest context ready i hi
  | .name name shape :: rest, context, ready => by
    simp only [constGlobalDecls] at ready
    intro i hi
    simp only [compileDecsExactHOL] at hi
    exact globals_constStores rest context ready i hi

/-- One constant store costs 289: `TopAddr` address 128, constant 19, one
stored word 142. -/
theorem globals_constStore_score (B : Nat) {F : Type} {s post : PanSemStateFiniteExact 64 F}
    {address word : BitVec 64} {r ev}
    (run : StatementRun s (.store (.op .sub [.topAddr, .const address]) (.const word)) r post ev)
    (ok : r ≠ some .error) : sharpSourceScore B ev = 289 := by
  cases run
  case storeValue =>
    rename_i _ value _ aev vev _ dst src
    have addr := globals_address_events B dst
    have hv : value = .val (.word word) := by
      have := src.sound; simp [expressionValue, evalHOLExact] at this; exact this.symm
    subst hv
    have constPrice : sourcePrice s (.const word) = 19 := by
      simp [sourcePrice, sourcePrices, exprPrices]
    rw [src.events_eq, srcScore_statement, sharpSourceScore_append, sharpSourceScore_append,
      srcScore_expressionEvents, constPrice]
    simp only [flattenHOL, List.length_singleton, srcScore_memory, sharpSourceScore_nil,
      globalAddressPrice] at addr ⊢
    omega
  all_goals exact absurd rfl ok

/-- The initialiser block of the generated entry costs `289` per store; the
final `Skip` is free. -/
theorem globals_inits_score (B : Nat) {F : Type} :
    ∀ (inits : List (ProgHOL 64)) {s post : PanSemStateFiniteExact 64 F} {r ev},
      ConstStores inits → StatementRun s (nestedSeqHOL inits) r post ev → r ≠ some .error →
        sharpSourceScore B ev ≤ 289 * inits.length
  | [], _, _, _, _, _, run, _ => by
    cases run
    simp [srcScore_statement, sharpSourceScore_nil]
  | i :: rest, _, _, _, _, stores, run, ok => by
    obtain ⟨address, word, rfl⟩ := stores i (by simp)
    have restStores : ConstStores rest := fun j hj => stores j (by simp [hj])
    simp only [nestedSeqHOL] at run
    cases run with
    | seqNext one two =>
      have a := globals_constStore_score B one (by simp)
      have b := globals_inits_score B rest restStores two ok
      gsimp
      simp only [List.length_cons]
      omega
    | seqStop terminal one =>
      cases one
      all_goals first | exact absurd rfl ok | exact absurd rfl terminal

#print axioms globals_constStores
#print axioms globals_inits_score
end InitECandidate.Runtime.FineCost
