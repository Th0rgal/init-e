import InitECandidate.Runtime.AllocCostExecuted
import InitECandidate.Runtime.AllocCostReconcile
import InitECandidate.Runtime.AllocCostSSAControl
namespace InitECandidate.Runtime.FineCost
open Flapjack Flapjack.Compiler.Backend.WordAlloc Flapjack.WordSemStateFiniteExact
open InitECandidate.Runtime.WordToStack

/-!
# Executed SSA reconciliation budgets

The `AllocCostReconcile` and `AllocCostSSAControl` modules bound the *syntax*
that SSA inserts.  This module connects those insertions to the actual
`wordPathWork` trace at the state where they run.

The key point is that a reconciliation move is charged at the state of the
actual loop iteration or exit that executes it.  The loop body/back-edge lemma
below therefore charges the back-edge move at the actual intermediate state of
that iteration; it is not a once-per-loop syntax allowance.  The remaining
missing premise is the well-founded induction over the whole loop's actual
iteration sequence, which is stated explicitly in the documentation and is not
hidden in these theorems.
-/

theorem foldrSeqStraight (programs : List (WordLangProgHOL (BitVec 64)))
    (allStraight : ∀ p ∈ programs, wordStraightFragment p = true) :
    wordStraightFragment (programs.foldr .seq .skip) = true := by
  induction programs with
  | nil => simp [wordStraightFragment]
  | cons head tail ih =>
    have headStraight : wordStraightFragment head = true := allStraight head (by simp)
    have tailStraight : ∀ p ∈ tail, wordStraightFragment p = true := by
      intro p member
      exact allStraight p (by simp [member])
    simp only [List.foldr_cons, wordStraightFragment, headStraight, ih tailStraight]
    rfl

theorem ssaReconcile_straight (cur target : Spt Nat) {β : Type} (names : Spt β) :
    wordStraightFragment (ssaReconcile (width := 64) cur target names) = true := by
  unfold ssaReconcile
  dsimp only
  split <;> simp [wordStraightFragment]

theorem loopSetup_straight (names exitNames : Spt Unit) (ssa : Spt Nat) (next : Nat) :
    wordStraightFragment (loopSetup (width := 64) names exitNames ssa next).1 = true := by
  unfold loopSetup
  dsimp only
  rcases listNextVarRename
    (((sptToAList (sptUnion names exitNames)).map Prod.fst).filter
      (fun v => (sptLookup v ssa).isNone)) ssa next with ⟨freshNames, ssaExt, naExt⟩
  rcases hrefresh : listNextVarRenameMove (width := 64) ssaExt naExt
    (((sptToAList (sptUnion names exitNames)).map Prod.fst).filter
      (fun v => (sptLookup v ssa).isSome)) with ⟨refreshMove, ssaRefreshed, naRefreshed⟩
  have refreshStraight : wordStraightFragment refreshMove = true := by
    rw [show refreshMove = (listNextVarRenameMove (width := 64) ssaExt naExt
      (((sptToAList (sptUnion names exitNames)).map Prod.fst).filter
        (fun v => (sptLookup v ssa).isSome))).1 from
        (congrArg Prod.fst hrefresh).symm]
    unfold listNextVarRenameMove
    dsimp only
    simp [wordStraightFragment]
  dsimp only
  simp only [wordStraightFragment, Bool.and_eq_true]
  constructor
  · apply foldrSeqStraight
    intro p member
    rcases List.mem_map.mp member with ⟨name, _, rfl⟩
    simp [fakeMove, wordStraightFragment]
  · exact refreshStraight

/-- The reconciliation move actually executed at an exit costs at most the
current live-name set, at every concrete state. -/
theorem ssaReconcile_executed_le {C F : Type}
    (cur target : Spt Nat) {β : Type} (names : Spt β)
    (state : WordSemStateFiniteExact 64 C F) :
    wordPathWork (ssaReconcile (width := 64) cur target names) state ≤
      1 + (sptToAList names).length := by
  exact Nat.le_trans
    (wordPathWork_le_nodeCost_straight (ssaReconcile (width := 64) cur target names) state
      (ssaReconcile_straight cur target names))
    (ssaReconcile_nodeCost_le cur target names)

/-- Loop setup actually executed before the first iteration. -/
theorem loopSetup_executed_le {C F : Type}
    (names exitNames : Spt Unit) (ssa : Spt Nat) (next : Nat)
    (state : WordSemStateFiniteExact 64 C F) :
    wordPathWork (loopSetup (width := 64) names exitNames ssa next).1 state ≤
      3 + 3 * (sptToAList (sptUnion names exitNames)).length := by
  exact Nat.le_trans
    (wordPathWork_le_nodeCost_straight (loopSetup (width := 64) names exitNames ssa next).1 state
      (loopSetup_straight names exitNames ssa next))
    (loopSetup_nodeCost_le names exitNames ssa next)

/-- One actual loop iteration: the body runs, then the back-edge reconciliation
runs at the actual intermediate state.  This is the per-execution charge; no
whole-loop syntax maximum is used. -/
theorem loopBodyFinal_executed_le {C F : Type}
    (body : WordLangProgHOL (BitVec 64)) (back : WordLangProgHOL (BitVec 64))
    (state : WordSemStateFiniteExact 64 C F) {β : Type} (names : Spt β)
    (backBound : ∀ middle : WordSemStateFiniteExact 64 C F,
      wordPathWork back middle ≤ 1 + (sptToAList names).length) :
    wordPathWork (match back with
      | .skip => body
      | _ => body.seq back) state ≤
      wordPathWork body state + ((sptToAList names).length + 2) := by
  split
  · omega
  · rename_i nonempty
    rw [wordPathWork_seq]
    cases run : evaluate body state with
    | mk result middle =>
      cases result with
      | none =>
        have := backBound middle
        dsimp only
        omega
      | some value =>
        dsimp only
        omega

/-- The actual executed reconciliation before a `break`/`continue` exit. -/
theorem exitAfterMoves_executed_le {C F : Type}
    (moves exit : WordLangProgHOL (BitVec 64))
    (state : WordSemStateFiniteExact 64 C F)
    {β : Type} (names : Spt β)
    (movesBound : wordPathWork moves state ≤ 1 + (sptToAList names).length)
    (exitOne : ∀ middle : WordSemStateFiniteExact 64 C F, wordPathWork exit middle = 1) :
    wordPathWork (match moves with
      | .skip => exit
      | _ => moves.seq exit) state ≤
      (sptToAList names).length + 4 := by
  split
  · have := exitOne state
    omega
  · rw [wordPathWork_seq]
    cases run : evaluate moves state with
    | mk result middle =>
      cases result with
      | none =>
        have := exitOne middle
        dsimp only
        omega
      | some value =>
        dsimp only
        omega

#print axioms foldrSeqStraight
#print axioms ssaReconcile_straight
#print axioms loopSetup_straight
#print axioms ssaReconcile_executed_le
#print axioms loopSetup_executed_le
#print axioms loopBodyFinal_executed_le
#print axioms exitAfterMoves_executed_le
end InitECandidate.Runtime.FineCost
