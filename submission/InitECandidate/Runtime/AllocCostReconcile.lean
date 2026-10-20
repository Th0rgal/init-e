import InitECandidate.Runtime.AllocCostSSA
import Flapjack.Compiler.Backend.WordAlloc.SSAHelpers
import Flapjack.Compiler.Backend.WordAlloc.SSAFixInconsistencies
namespace InitECandidate.Runtime.FineCost
open Flapjack Flapjack.Compiler.Backend.WordAlloc
open InitECandidate.Runtime.WordToStack

/-!
# SSA reconciliation move budgets

These are the dynamic, per-site budgets for the moves SSA inserts at loop
headers, loop back-edges, calls, exception handlers, `break` and `continue`.
Every budget is a function of the actual live-name list or renaming-map domain
at that site; none is a whole-program AST, code-table or bitmap maximum.
-/

theorem listNextVarRenameMove_nodeCost (ssa : Spt Nat) (next : Nat) (names : List Nat) :
    wordNodeCost (listNextVarRenameMove (width := 64) ssa next names).1 = 1 + names.length := by
  simp only [listNextVarRenameMove, wordNodeCost, List.length_zip, listNextVarRename_length,
    List.length_map]
  omega

/-- The reconciliation move list is no longer than the live-name list. -/
theorem ssaReconcile_length (cur target : Spt Nat) {β : Type} (names : Spt β) :
    let vars := (sptToAList names).map Prod.fst
    let moves := ((vars.map fun v =>
        match sptLookup v cur with
        | none => []
        | some curV => [(optionLookup target v, curV)]).flatten).filter
      (fun x => decide (x.1 ≠ x.2))
    moves.length ≤ vars.length := by
  let selector : Nat → List (Nat × Nat) := fun v =>
    match sptLookup v cur with
    | none => []
    | some curV => [(optionLookup target v, curV)]
  let vars := (sptToAList names).map Prod.fst
  have flatBound : ((vars.map selector).flatten).length ≤ vars.length := by
    induction vars with
    | nil => simp
    | cons v rest ih =>
      have single : (selector v).length ≤ 1 := by
        simp only [selector]
        split <;> simp
      simp only [List.map_cons, List.flatten_cons, List.length_append, List.length_cons]
      omega
  have filterBound := List.length_filter_le
    (fun pair : Nat × Nat => decide (pair.1 ≠ pair.2))
    ((vars.map selector).flatten)
  exact Nat.le_trans filterBound flatBound

theorem ssaReconcile_nodeCost_le (cur target : Spt Nat) {β : Type} (names : Spt β) :
    wordNodeCost (ssaReconcile (width := 64) cur target names) ≤
      1 + (sptToAList names).length := by
  have bound := ssaReconcile_length cur target names
  unfold ssaReconcile
  dsimp only
  split
  · simp [wordNodeCost] <;> omega
  · simp only [wordNodeCost]
    have varsLength : ((sptToAList names).map Prod.fst).length = (sptToAList names).length := by
      simp
    dsimp only at bound
    rw [varsLength] at bound
    exact Nat.add_le_add_left bound 1

/-- Both lists produced by `mergeMoves` are bounded by the name list. -/
theorem mergeMoves_length_le (names : List Nat) (left right : Spt Nat) (next : Nat) :
    (mergeMoves names left right next).1.length ≤ names.length ∧
      (mergeMoves names left right next).2.1.length ≤ names.length := by
  induction names generalizing left right next with
  | nil => simp [mergeMoves]
  | cons name rest ih =>
    have ih' := ih left right next
    simp only [mergeMoves]
    rcases hrec : mergeMoves rest left right next with ⟨leftMoves, rightMoves, next', leftMap, rightMap⟩
    rw [hrec] at ih'
    dsimp only at ih'
    split <;> (try split) <;> (try dsimp only) <;> simp only [List.length_cons] <;> omega

/-- `fakeMoves` emits at most six local nodes per live name, both sides
together. -/
theorem fakeMoves_nodeCost_le (priority : Option (Unit ⊕ Unit)) (names : List Nat)
    (left right : Spt Nat) (next : Nat) :
    let result := fakeMoves (width := 64) priority names left right next
    wordNodeCost result.1 + wordNodeCost result.2.1 ≤ 2 + 6 * names.length := by
  induction names generalizing left right next with
  | nil => simp [fakeMoves, wordNodeCost]
  | cons name rest ih =>
    have ih' := ih left right next
    simp only [fakeMoves]
    rcases hrec : fakeMoves (width := 64) priority rest left right next with
      ⟨leftSeq, rightSeq, next', leftMap, rightMap⟩
    rw [hrec] at ih'
    dsimp only at ih'
    split
    all_goals
      try split
      try dsimp only
      simp [wordNodeCost, fakeMove, List.length_cons]
      omega

/-- `fixInconsistencies` costs at most eight nodes per union key plus six. -/
theorem fixInconsistencies_nodeCost_le (priority : Option (Unit ⊕ Unit))
    (left right : Spt Nat) (next : Nat) :
    let result := fixInconsistencies (width := 64) priority left right next
    wordNodeCost result.1 + wordNodeCost result.2.1 ≤
      6 + 8 * (sptToAList (sptUnion left right)).length := by
  unfold fixInconsistencies
  rcases hmerge : mergeMoves ((sptToAList (sptUnion left right)).map Prod.fst) left right next with
    ⟨leftMoves, rightMoves, next', leftMap, rightMap⟩
  rcases hfake : fakeMoves (width := 64) priority ((sptToAList (sptUnion left right)).map Prod.fst)
    leftMap rightMap next' with ⟨leftSeq, rightSeq, next'', leftMap', rightMap'⟩
  have mergeBound := mergeMoves_length_le
    ((sptToAList (sptUnion left right)).map Prod.fst) left right next
  rw [hmerge] at mergeBound
  dsimp only at mergeBound
  have fakeBound := fakeMoves_nodeCost_le priority
    ((sptToAList (sptUnion left right)).map Prod.fst) leftMap rightMap next'
  rw [hfake] at fakeBound
  dsimp only at fakeBound
  have varsLength : ((sptToAList (sptUnion left right)).map Prod.fst).length =
      (sptToAList (sptUnion left right)).length := by
    simp
  dsimp only
  rw [hmerge, hfake]
  simp only [Prod.fst, Prod.snd, wordNodeCost]
  omega

theorem foldrSeqSkip_nodeCost (programs : List (WordLangProgHOL (BitVec 64)))
    (allOne : ∀ p ∈ programs, wordNodeCost p = 1) :
    wordNodeCost (programs.foldr .seq .skip) = 2 * programs.length + 1 := by
  induction programs with
  | nil => simp [wordNodeCost]
  | cons head tail ih =>
    have headOne : wordNodeCost head = 1 := allOne head (by simp)
    have tailOne : ∀ p ∈ tail, wordNodeCost p = 1 := by
      intro p member
      exact allOne p (by simp [member])
    simp only [List.foldr_cons, wordNodeCost, List.length_cons]
    rw [ih tailOne, headOne]
    omega

/-- Loop setup: fake fresh-position constants and one refresh move. -/
theorem loopSetup_nodeCost_le (names exitNames : Spt Unit) (ssa : Spt Nat) (next : Nat) :
    wordNodeCost (loopSetup (width := 64) names exitNames ssa next).1 ≤
      3 + 3 * (sptToAList (sptUnion names exitNames)).length := by
  unfold loopSetup
  dsimp only
  rcases hfresh : listNextVarRename
    (((sptToAList (sptUnion names exitNames)).map Prod.fst).filter
      (fun v => (sptLookup v ssa).isNone)) ssa next with ⟨freshNames, ssaExt, naExt⟩
  rcases hrefresh : listNextVarRenameMove (width := 64) ssaExt naExt
    (((sptToAList (sptUnion names exitNames)).map Prod.fst).filter
      (fun v => (sptLookup v ssa).isSome)) with ⟨refreshMove, ssaRefreshed, naRefreshed⟩
  have freshLength := listNextVarRename_length
    (((sptToAList (sptUnion names exitNames)).map Prod.fst).filter
      (fun v => (sptLookup v ssa).isNone)) ssa next
  rw [hfresh] at freshLength
  dsimp only at freshLength
  have refreshLength := listNextVarRenameMove_nodeCost ssaExt naExt
    (((sptToAList (sptUnion names exitNames)).map Prod.fst).filter
      (fun v => (sptLookup v ssa).isSome))
  rw [hrefresh] at refreshLength
  dsimp only at refreshLength
  have fakeCost : wordNodeCost ((freshNames.map (fun r => fakeMove (width := 64) r)).foldr .seq .skip) =
      2 * freshNames.length + 1 := by
    have h := foldrSeqSkip_nodeCost (freshNames.map (fun r => fakeMove (width := 64) r)) (by
      intro p member
      rcases List.mem_map.mp member with ⟨name, _, rfl⟩
      simp [fakeMove, wordNodeCost])
    simpa using h
  have allVarsLength : ((sptToAList (sptUnion names exitNames)).map Prod.fst).length =
      (sptToAList (sptUnion names exitNames)).length := by simp
  have freshLe : freshNames.length ≤
      (sptToAList (sptUnion names exitNames)).length := by
    rw [freshLength]
    exact Nat.le_trans (List.length_filter_le _ _) (by omega)
  have refreshLe : (((sptToAList (sptUnion names exitNames)).map Prod.fst).filter
      (fun v => (sptLookup v ssa).isSome)).length ≤
      (sptToAList (sptUnion names exitNames)).length :=
    Nat.le_trans (List.length_filter_le _ _) (by omega)
  simp only [wordNodeCost]
  omega

#print axioms loopSetup_nodeCost_le
#print axioms fixInconsistencies_nodeCost_le
#print axioms fakeMoves_nodeCost_le
#print axioms mergeMoves_length_le
#print axioms ssaReconcile_nodeCost_le
#print axioms listNextVarRenameMove_nodeCost
end InitECandidate.Runtime.FineCost
