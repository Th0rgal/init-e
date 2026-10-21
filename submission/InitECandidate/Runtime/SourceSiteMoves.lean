import InitECandidate.Runtime.AllocFunctionTables
import InitECandidate.Runtime.CallSiteTable
import InitECandidate.Runtime.TailSiteTable
import InitE.SourceDeclarationsCore
import Flapjack.Pancake.PanGlobals
namespace InitECandidate.Runtime.FineCost
open Flapjack Flapjack.Pancake.PanLang

/-! Source charges for the allocator moves of the pinned allocated program. A
statement executing in the body of source function `fn` pays the move table of
`fn`'s allocated label (`AllocFunctionTables`): a call pays the table entry for
its callee, an `if` the branch-merge maximum, a `while` iteration the loop
reconcile and branch-merge maxima, a `return` or `raise` the move run before it.
Function names are what every source pass preserves, so the charges are the
same on both sides of `pan_simp` and `pan_globals`. -/

/-- Functions of the source program, in the compiler's order. -/
def sourceFunctions : List (FunDeclHOL 64) :=
  InitE.sourceDeclarations.filterMap (fun d => match d with | .function f => some f | _ => none)

/-- The allocated label of the `i`-th source function. -/
def sourceLabel (i : Nat) : Nat := 65 + i

/-- The source entry name. -/
def entryName : MlS := Flapjack.Basis.Pure.MlString.ofString "main"

/-- The fresh name `pan_globals` gives the source entry (`main'`), whose
compiled body is the source entry's. -/
def freshEntryName : MlS :=
  Flapjack.Basis.Pure.MlString.MlString.implode [109#8, 97#8, 105#8, 110#8, 39#8]

/-- Names as the allocated labels see them: the renamed entry is the entry. -/
def canonicalName (name : MlS) : MlS := if name = freshEntryName then entryName else name

/-- The allocated label of a source function name. -/
def functionLabel (name : MlS) : Option Nat :=
  (sourceFunctions.findIdx? (fun f => f.name = canonicalName name)).map sourceLabel

/-- The allocated label whose table a statement of `fn` pays: the entry wrapper
(64) for a name outside the source functions. -/
def fnLabel (fn : MlS) : Nat := (functionLabel fn).getD 64

/-- Moves charged to a call of `callee` from `fn`. -/
def callMoves (fn callee : MlS) : Nat := (tableOf (fnLabel fn)).call (functionLabel callee)

/-- WordSimp constant re-insert surcharge charged to a call of `callee` from
`fn`: the certified caller+callee table entry (`CallSiteTable`), in Word price
units, plus the callee's certified tail-call surcharge (`TailSiteTable`). Kept
separate from the allocator moves. -/
def callSites (fn callee : MlS) : Nat :=
  24 * (callTabGet (fnLabel fn, functionLabel callee) + callTabGet (fnLabel fn, none)) +
    ((functionLabel callee).map srcTailSitesL).getD 0

/-- Branch-merge moves charged to an `if` of `fn`. -/
def branchMoves (fn : MlS) : Nat := (tableOf (fnLabel fn)).merge

/-- Loop moves charged to each `while` iteration of `fn`. -/
def loopMoves (fn : MlS) : Nat := (tableOf (fnLabel fn)).loop + (tableOf (fnLabel fn)).merge

/-- Moves before a `return` of `fn`. -/
def returnMoves (fn : MlS) : Nat := (tableOf (fnLabel fn)).ret

/-- Moves before a `raise` of `fn`. -/
def raiseMoves (fn : MlS) : Nat := (tableOf (fnLabel fn)).raise

/-- A loop iteration pays the branch-merge maximum too. -/
theorem branchMoves_le_loopMoves (fn : MlS) : branchMoves fn ≤ loopMoves fn := by
  simp only [branchMoves, loopMoves]; omega

/-- A name permutation that keeps every label: charges are unchanged. -/
def LabelInvariant (f g : MlS) : Prop := ∀ n, functionLabel (fpermName f g n) = functionLabel n

theorem fnLabel_fperm {f g : MlS} (h : LabelInvariant f g) (n : MlS) :
    fnLabel (fpermName f g n) = fnLabel n := by simp only [fnLabel, h n]

theorem callMoves_fperm {f g : MlS} (h : LabelInvariant f g) (a b : MlS) :
    callMoves (fpermName f g a) (fpermName f g b) = callMoves a b := by
  simp only [callMoves, fnLabel_fperm h, h b]

theorem callSites_fperm {f g : MlS} (h : LabelInvariant f g) (a b : MlS) :
    callSites (fpermName f g a) (fpermName f g b) = callSites a b := by
  simp only [callSites, fnLabel_fperm h, h b]

theorem branchMoves_fperm {f g : MlS} (h : LabelInvariant f g) (a : MlS) :
    branchMoves (fpermName f g a) = branchMoves a := by simp only [branchMoves, fnLabel_fperm h]

theorem loopMoves_fperm {f g : MlS} (h : LabelInvariant f g) (a : MlS) :
    loopMoves (fpermName f g a) = loopMoves a := by simp only [loopMoves, fnLabel_fperm h]

theorem returnMoves_fperm {f g : MlS} (h : LabelInvariant f g) (a : MlS) :
    returnMoves (fpermName f g a) = returnMoves a := by simp only [returnMoves, fnLabel_fperm h]

theorem raiseMoves_fperm {f g : MlS} (h : LabelInvariant f g) (a : MlS) :
    raiseMoves (fpermName f g a) = raiseMoves a := by simp only [raiseMoves, fnLabel_fperm h]

theorem canonicalName_fperm (n : MlS) :
    canonicalName (fpermName entryName freshEntryName n) = canonicalName n := by
  have ne : entryName ≠ freshEntryName := by decide
  unfold fpermName canonicalName
  by_cases h1 : entryName = n
  · subst h1; simp [ne, Ne.symm ne]
  · by_cases h2 : freshEntryName = n
    · subst h2; simp [ne, Ne.symm ne]
    · simp [h1, h2, Ne.symm h1, Ne.symm h2]

/-- The guest's entry renaming keeps every label. -/
theorem labelInvariant_entry : LabelInvariant entryName freshEntryName := by
  intro n
  simp only [functionLabel, canonicalName_fperm]

#print axioms branchMoves_le_loopMoves
#print axioms callMoves_fperm
#print axioms callSites_fperm
#print axioms labelInvariant_entry
end InitECandidate.Runtime.FineCost
