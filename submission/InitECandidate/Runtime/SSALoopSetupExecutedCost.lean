import InitECandidate.Runtime.SSALoopBodyEntry
import InitECandidate.Runtime.AllocCostSSA
import Flapjack.Compiler.Backend.WordAlloc.Proofs.SSALoopSetup

namespace InitECandidate.Runtime.FineCost
open Flapjack Flapjack.Compiler.Backend Flapjack.Compiler.Backend.WordAlloc
open Flapjack.WordSemStateFiniteExact
set_option maxHeartbeats 4000000

/-- A static straight-fragment budget pays only the actually reached suffix. -/
theorem optimizer_seq_budget {C F : Type} (first second : WordLangProgHOL (BitVec 64))
    (a b : Nat) (one : ∀ s : WordSemStateFiniteExact 64 C F,
      wordExecutionCost wordOptimizerLocalPrice first s ≤ a)
    (two : ∀ s : WordSemStateFiniteExact 64 C F,
      wordExecutionCost wordOptimizerLocalPrice second s ≤ b)
    (source : WordSemStateFiniteExact 64 C F) :
    wordExecutionCost wordOptimizerLocalPrice (.seq first second) source ≤ a + b := by
  rw [wordExecutionCost_seq]
  have head : wordOptimizerLocalPrice (.seq first second) source = 0 := rfl
  rw [head, Nat.zero_add]
  rcases actual : evaluate first source with ⟨result, middle⟩
  cases result with
  | none => exact Nat.add_le_add (one source) (two middle)
  | some result => simpa only [Nat.add_zero] using (one source).trans (Nat.le_add_right a b)

/-- Each actual fake initialization is one constant at the optimizer price. -/
theorem optimizer_fake_chain_cost {C F : Type} (registers : List Nat)
    (source : WordSemStateFiniteExact 64 C F) :
    wordExecutionCost wordOptimizerLocalPrice
      ((registers.map fun r => (fakeMove r : WordLangProgHOL (BitVec 64))).foldr .seq .skip) source ≤
      24 * registers.length := by
  induction registers generalizing source with
  | nil => simp [wordExecutionCost, wordOptimizerLocalPrice,
      WordToStack.refinedWordLocalPrice, WordToStack.refinedWordStackLeafBudget]
  | cons register rest ih =>
    simp only [List.map_cons, List.foldr_cons, List.length_cons]
    have step := optimizer_seq_budget (fakeMove register)
      ((rest.map fun r => (fakeMove r : WordLangProgHOL (BitVec 64))).foldr .seq .skip)
      24 (24 * rest.length) (fun s => by
        simp [fakeMove, wordExecutionCost, wordOptimizerLocalPrice, WordToStack.refinedWordLocalPrice,
          WordToStack.refinedWordStackLeafBudget, WordToStack.refinedNativeInstructionPrice,
          Compiler.Encoders.Asm.HolInst.ofWordLangInst]) ih source
    omega

theorem optimizer_refresh_move_cost {C F : Type} (map : Spt Nat) (next : Nat) (names : List Nat)
    (source : WordSemStateFiniteExact 64 C F) :
    wordExecutionCost wordOptimizerLocalPrice (listNextVarRenameMove (width := 64) map next names).1 source =
      24 * names.length := by
  simp only [listNextVarRenameMove, wordExecutionCost, wordOptimizerLocalPrice, List.length_zip,
    List.length_map, listNextVarRename_length, Nat.min_self]

private theorem lookup_partition_length (keys : List Nat) (map : Spt Nat) :
    (keys.filter (fun key => (sptLookup key map).isNone)).length +
      (keys.filter (fun key => (sptLookup key map).isSome)).length = keys.length := by
  induction keys with
  | nil => rfl
  | cons key rest ih => cases found : sptLookup key map <;> simp [found, ih, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]

/-- Loop setup costs one optimizer unit of24 for each fresh initialization or
refresh pair. These lists partition the actual live-name union, so setup is
paid once by that union, with no fuel or AST-size multiplier. -/
theorem optimizer_loop_setup_cost {C F : Type} (names exits : Spt Unit) (map : Spt Nat) (next : Nat)
    (source : WordSemStateFiniteExact 64 C F) :
    wordExecutionCost wordOptimizerLocalPrice (loopSetup (width := 64) names exits map next).1 source ≤
      24 * (sptToAList (sptUnion names exits)).length := by
  unfold loopSetup
  dsimp only
  generalize keysEq : (sptToAList (sptUnion names exits)).map Prod.fst = keys
  have partition := lookup_partition_length keys map
  rcases produced : listNextVarRename (keys.filter (fun v => (sptLookup v map).isNone)) map next with
    ⟨registers, extended, nextExtended⟩
  dsimp only
  have length := listNextVarRename_length (keys.filter (fun v => (sptLookup v map).isNone)) map next
  rw [produced] at length
  have bound := optimizer_seq_budget _ _ (24 * registers.length)
    (24 * (keys.filter (fun v => (sptLookup v map).isSome)).length)
    (fun s => optimizer_fake_chain_cost registers s)
    (fun s => le_of_eq (optimizer_refresh_move_cost extended nextExtended _ s)) source
  have keysLength : keys.length = (sptToAList (sptUnion names exits)).length := by
    rw [← keysEq, List.length_map]
  dsimp only at length
  omega

/-- The actual pinned setup run, original complete frame and SSA map facts,
plus the discharged executed work and refreshed strong loop-head relation. -/
theorem loopSetupCorrect_cost {C F : Type}
    (source target : WordSemStateFiniteExact 64 C F) (map : Spt Nat) (next : Nat)
    (names exits : Spt Unit) (setup : WordLangProgHOL (BitVec 64)) (refreshed : Spt Nat) (nextRefreshed : Nat)
    (frame : Flapjack.WordAlloc.wordStateEqRel source target)
    (related : ssaLocalsRel next map source.locals target.locals)
    (valid : ssaMapOK next map) (allocated : isAllocVar next)
    (produced : loopSetup names exits map next = (setup, refreshed, nextRefreshed)) :
    ∃ after, evaluate setup target = (none, after) ∧
      Flapjack.WordAlloc.wordStateEqRel source after ∧
      ssaLocalsRel nextRefreshed refreshed source.locals after.locals ∧
      Flapjack.WordAlloc.strongLocalsRel (optionLookup refreshed) (sptDomain names) source.locals after.locals ∧
      next ≤ nextRefreshed ∧ isAllocVar nextRefreshed ∧ ssaMapOK nextRefreshed refreshed ∧
      sptDomain refreshed = (fun key => sptDomain map key ∨ sptDomain (sptUnion names exits) key) ∧
      (∀ x y, sptDomain names x → sptDomain names y →
        optionLookup refreshed x = optionLookup refreshed y → x = y) ∧
      (∀ x y, sptDomain exits x → sptDomain exits y →
        optionLookup refreshed x = optionLookup refreshed y → x = y) ∧
      (∀ key, sptDomain refreshed key → sptDomain after.locals (optionLookup refreshed key)) ∧
      wordExecutionCost wordOptimizerLocalPrice setup target ≤ 24 * (sptToAList (sptUnion names exits)).length := by
  obtain ⟨after, run, frameAfter, locals, grows, allocAfter, validAfter, domain, entryInj, exitInj, present⟩ :=
    loopSetupCorrect source target map next names exits setup refreshed nextRefreshed
      ⟨frame, related, valid, allocated, produced⟩
  have cost := optimizer_loop_setup_cost names exits map next target
  rw [produced] at cost
  exact ⟨after, run, frameAfter, locals, ssa_locals_strong _ _ _ _ _ locals,
    grows, allocAfter, validAfter, domain, entryInj, exitInj, present, cost⟩

#print axioms optimizer_fake_chain_cost
#print axioms optimizer_refresh_move_cost
#print axioms optimizer_loop_setup_cost
#print axioms loopSetupCorrect_cost
end InitECandidate.Runtime.FineCost
