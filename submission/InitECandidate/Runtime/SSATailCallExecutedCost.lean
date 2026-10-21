import InitECandidate.Runtime.SSAQuantitativeCost
import Flapjack.Compiler.Backend.WordAlloc.Proofs.SSASemanticCallTail
namespace InitECandidate.Runtime.FineCost
open Flapjack Flapjack.Compiler.Backend Flapjack.Compiler.Backend.WordAlloc
open Flapjack.WordSemStateFiniteExact
set_option maxHeartbeats 6000000

theorem ssa_tail_arguments {width : Nat} [NeZero width] {C F : Type}
    (source target : WordSemStateFiniteExact width C F) (ssa : Spt Nat) (next : Nat)
    (args : List Nat) (values : List (WordLocW width))
    (related : ssaLocalsRel next ssa source.locals target.locals)
    (read : WordSemStateFiniteExact.getVars args source = some values) :
    let renamed := args.map (optionLookup ssa)
    let registers := (List.range renamed.length).map fun key => 2 * key
    WordSemStateFiniteExact.evaluate (.move 1 (registers.zip renamed)) target =
      (none,WordSemStateFiniteExact.setVars registers values target) ∧
    WordSemStateFiniteExact.getVars registers
      (WordSemStateFiniteExact.setVars registers values target) = some values := by
  dsimp only
  let renamed := args.map (optionLookup ssa)
  let registers := (List.range renamed.length).map fun key => 2 * key
  have lengths := Flapjack.WordAlloc.getVarsLength args source values read
  have distinct : registers.Nodup := by
    apply List.Nodup.map _ List.nodup_range
    intro x y equal
    change 2 * x = 2 * y at equal
    omega
  have same : registers.length = renamed.length := by simp [registers]
  have valuesLength : values.length = registers.length := by simp [registers,renamed,lengths]
  have renamedRead := ssaLocalsRelGetVars args values next ssa source target ⟨related,read⟩
  change WordSemStateFiniteExact.evaluate (.move 1 (registers.zip renamed)) target =
    (none,WordSemStateFiniteExact.setVars registers values target) ∧ _
  constructor
  · simp only [WordSemStateFiniteExact.evaluate,List.map_fst_zip (Nat.le_of_eq same),
      List.map_snd_zip (Nat.le_of_eq same.symm),distinct,if_true]
    rw [show WordSemStateFiniteExact.getVars renamed target = some values from renamedRead]
  · exact getVarsSetVarsEq registers values target ⟨distinct,valuesLength⟩


/-- Private reduction of Call_tail's destination guard. The generated convention
register list is empty exactly when the original argument list is empty; this
is proof factoring, not a separately tagged HOL declaration. -/
theorem ssa_tail_destination_guard (dest : Option Nat) (args : List Nat)
    (ssa : Spt Nat) :
    wordSemBadDestArgs dest
      ((List.range (args.map (optionLookup ssa)).length).map fun key => 2 * key) =
      wordSemBadDestArgs dest args := by
  cases args <;> simp [wordSemBadDestArgs]


/-- Static local price of the actual tail-call argument preparation and call.
The callee execution is counted separately, at its actual entry state. -/
def ssaTailLocalPrice (price : WordLangProgHOL (BitVec 64) → Nat)
    (dest : Option Nat) (args : List Nat) (map : Spt Nat) : Nat :=
  let renamed := args.map (optionLookup map)
  let registers := (List.range renamed.length).map fun key => 2 * key
  let moves := WordLangProgHOL.move 1 (registers.zip renamed)
  let call := WordLangProgHOL.call none dest registers none
  price (.seq moves call) + price moves + price call

/-- Actual SSA tail-call work. Both executions enter exactly the SAME callee;
there is no recursive compiler IH or assumed callee budget. The pure-price
comparison is pointwise and the only extra caller charge is static emitted
argument preparation. This uses the target scheduler as the source witness. -/
theorem ssa_tail_call_executed_cost {C F : Type}
    (SP TP : WordLangProgHOL (BitVec 64) → Nat)
    (source target : WordSemStateFiniteExact 64 C F)
    (map : Spt Nat) (next : Nat) (dest : Option Nat) (args : List Nat)
    (tables : List (Spt Nat × Spt Unit × Spt Unit))
    (frame : Flapjack.WordAlloc.wordStateEqRel source target)
    (locals : ssaLocalsRel next map source.locals target.locals)
    (prices : ∀ p, TP p ≤ SP p)
    (localPrice : ssaTailLocalPrice TP dest args map ≤ SP (.call none dest args none))
    (safe : (evaluate (.call none dest args none) {source with permute := target.permute}).1 ≠ some .error) :
    wordExecutionCost (fun p _ => TP p) (ssaCcTrans (.call none dest args none) map next tables).1 target ≤
      wordExecutionCost (fun p _ => SP p) (.call none dest args none)
        {source with permute := target.permute} := by
  let permuted := {source with permute := target.permute}
  have related : Flapjack.WordAlloc.wordStateEqRel permuted target := by
    simpa [permuted, Flapjack.WordAlloc.wordStateEqRel] using frame
  change (evaluate (.call none dest args none) permuted).1 ≠ some .error at safe
  change _ ≤ wordExecutionCost (fun p _ => SP p) (.call none dest args none) permuted
  rcases read : getVars args permuted with _ | values
  · simp only [evaluate, read] at safe
    exact (safe rfl).elim
  by_cases bad : wordSemBadDestArgs dest args = true
  · simp only [evaluate, read, bad, if_true] at safe
    exact (safe rfl).elim
  have good : wordSemBadDestArgs dest args = false := Bool.eq_false_iff.mpr bad
  rcases found : wordSemFindCode dest values permuted.code permuted.stackSize with _ | ⟨calleeArgs, callee, size⟩
  · simp only [evaluate, read, good, Bool.false_eq_true, if_false, wordSemAddRetLoc, found] at safe
    exact (safe rfl).elim
  let renamed := args.map (optionLookup map)
  let registers := (List.range renamed.length).map fun key => 2 * key
  let moved := setVars registers values target
  have preparation := ssa_tail_arguments permuted target map next args values locals read
  have moveRun : evaluate (.move 1 (registers.zip renamed)) target = (none, moved) := preparation.1
  have reread : getVars registers moved = some values := preparation.2
  have guard : wordSemBadDestArgs dest registers = false := by
    rw [ssa_tail_destination_guard]; exact good
  have movedFrame : Flapjack.WordAlloc.wordStateEqRel permuted moved := by
    simpa [moved, setVars, Flapjack.WordAlloc.wordStateEqRel] using related
  have fields := movedFrame
  unfold Flapjack.WordAlloc.wordStateEqRel at fields
  have codeEq := fields.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have sizeEq := fields.2.2.2.2.2.2.1
  have clockEq := fields.2.2.2.2.2.2.2.2.2.2.2.2.1
  have calleeState : callEnv calleeArgs size (decClock moved) =
      callEnv calleeArgs size (decClock permuted) := by
    simpa [permuted, moved, setVars] using
      Flapjack.WordAlloc.callEnv_decClock_wsr movedFrame calleeArgs size
  have compiled : ssaCcTrans (width := 64) (.call none dest args none) map next tables =
      (.seq (.move 1 (registers.zip renamed)) (.call none dest registers none), map, next) := rfl
  rw [compiled]
  dsimp only
  rw [wordExecutionCost_seq, moveRun]
  simp only
  rw [wordExecutionCost_atomic _ (.move 1 (registers.zip renamed)) _ rfl]
  conv_lhs => arg 2; rw [wordExecutionCost]
  conv_rhs => rw [wordExecutionCost]
  simp only [read, reread, good, guard, Bool.false_eq_true, if_false, wordSemAddRetLoc,
    codeEq, sizeEq, found, clockEq, calleeState]
  have localBound : TP (.seq (.move 1 (registers.zip renamed)) (.call none dest registers none)) +
      TP (.move 1 (registers.zip renamed)) + TP (.call none dest registers none) ≤
      SP (.call none dest args none) := localPrice
  by_cases zero : permuted.clock = 0
  · simp only [zero, if_true, dite_true]
    exact localBound
  · simp only [zero, if_false, dite_false]
    have calleeCost := wordExecutionCost_mono (fun p (_ : WordSemStateFiniteExact 64 C F) => TP p)
      (fun p _ => SP p) (fun p _ => prices p) callee (callEnv calleeArgs size (decClock permuted))
    omega

#print axioms ssa_tail_arguments
#print axioms ssa_tail_call_executed_cost
end InitECandidate.Runtime.FineCost
