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

theorem fakeMoves_straight (prio : Option (Unit ⊕ Unit)) :
    ∀ (names : List Nat) (ssaL ssaR : Spt Nat) (next : Nat),
      wordStraightFragment (fakeMoves (width := 64) prio names ssaL ssaR next).1 = true ∧
      wordStraightFragment (fakeMoves (width := 64) prio names ssaL ssaR next).2.1 = true := by
  intro names
  induction names with
  | nil =>
    intro ssaL ssaR next
    simp [fakeMoves, wordStraightFragment]
  | cons x xs ih =>
    intro ssaL ssaR next
    unfold fakeMoves
    dsimp only
    obtain ⟨seqL, seqR, next', ssaL', ssaR', hrec⟩ :
      ∃ seqL seqR next' ssaL' ssaR',
        fakeMoves (width := 64) prio xs ssaL ssaR next =
          (seqL, seqR, next', ssaL', ssaR') := ⟨_, _, _, _, _, rfl⟩
    have ihSpec := ih ssaL ssaR next
    rw [hrec] at ihSpec
    dsimp only at ihSpec
    rw [hrec]
    dsimp only
    split <;> simp [wordStraightFragment, fakeMove, ihSpec.1, ihSpec.2]

theorem fixInconsistencies_straight (prio : Option (Unit ⊕ Unit))
    (ssaL ssaR : Spt Nat) (next : Nat) :
    wordStraightFragment (fixInconsistencies (width := 64) prio ssaL ssaR next).1 = true ∧
    wordStraightFragment (fixInconsistencies (width := 64) prio ssaL ssaR next).2.1 = true := by
  unfold fixInconsistencies
  dsimp only
  rcases hmerge : mergeMoves
    ((sptToAList (sptUnion ssaL ssaR)).map Prod.fst) ssaL ssaR next with
    ⟨lmov, rmov, next', ssaL', ssaR'⟩
  rcases hfake : fakeMoves (width := 64) prio
    ((sptToAList (sptUnion ssaL ssaR)).map Prod.fst) ssaL' ssaR' next' with
    ⟨lseq, rseq, next'', ssaL'', ssaR''⟩
  have hfakeStraight := fakeMoves_straight prio
    ((sptToAList (sptUnion ssaL ssaR)).map Prod.fst) ssaL' ssaR' next'
  rw [hfake] at hfakeStraight
  dsimp only at hfakeStraight
  simp only [wordStraightFragment, hfakeStraight.1, hfakeStraight.2]
  exact ⟨rfl, rfl⟩

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

/-- Both exception-handler reconciliation programs actually executed at the
current state.  This is the executed form of the `fixInconsistencies` budget:
the two programs together cost at most the actual union domain. -/
theorem fixInconsistencies_executed_le {C F : Type}
    (prio : Option (Unit ⊕ Unit)) (left right : Spt Nat) (next : Nat)
    (state : WordSemStateFiniteExact 64 C F) :
    let result := fixInconsistencies (width := 64) prio left right next
    wordPathWork result.1 state + wordPathWork result.2.1 state ≤
      6 + 8 * (sptToAList (sptUnion left right)).length := by
  dsimp only
  have straight := fixInconsistencies_straight prio left right next
  have first := wordPathWork_le_nodeCost_straight
    (fixInconsistencies (width := 64) prio left right next).1 state straight.1
  have second := wordPathWork_le_nodeCost_straight
    (fixInconsistencies (width := 64) prio left right next).2.1 state straight.2
  have cost := fixInconsistencies_nodeCost_le prio left right next
  dsimp only at cost
  omega

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
#print axioms fixInconsistencies_executed_le
#print axioms loopSetup_executed_le
#print axioms loopBodyFinal_executed_le
#print axioms exitAfterMoves_executed_le
end InitECandidate.Runtime.FineCost
