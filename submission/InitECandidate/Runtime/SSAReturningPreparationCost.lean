import InitECandidate.Runtime.SSALoopSetupExecutedCost
import Flapjack.Compiler.Backend.WordAlloc.Proofs.SSASemanticCallReturn
namespace InitECandidate.Runtime.FineCost
open Flapjack Flapjack.Compiler.Backend Flapjack.Compiler.Backend.WordAlloc
open Flapjack.WordSemStateFiniteExact
set_option maxHeartbeats 6000000

/-- The actual returning-call stack refresh and convention argument moves,
with all original preparation/cut/frame facts and their executed move work.
The budget scales with the actual live-name union and argument list lengths;
no desired target execution or callee budget is assumed. -/
theorem returningPrepareArguments_cost  {C F : Type}
    (source target : WordSemStateFiniteExact 64 C F) (ssa : Spt Nat) (next : Nat)
    (args : List Nat) (values : List (WordLocW 64)) (first second : Spt Unit)
    (sourceFirst sourceSecond : Spt (WordLocW 64))
    (cut : wordSemCutEnvs (first,second) source.locals = some (sourceFirst,sourceSecond))
    (read : WordSemStateFiniteExact.getVars args source = some values)
    (related : ssaLocalsRel next ssa source.locals target.locals)
    (allocated : isAllocVar next) (valid : ssaMapOK next ssa)
    (frame : Flapjack.WordAlloc.wordStateEqRel source target) :
    let (move,mapOut,counter) := listNextVarRenameMove (width := 64) ssa (next+2)
      ((sptToAList (sptUnion first second)).map Prod.fst)
    let (result,refreshed) := WordSemStateFiniteExact.evaluate move target
    let renamed := args.map (optionLookup ssa)
    let registers := (List.range renamed.length).map fun key => 2*(key+1)
    let prepared := WordSemStateFiniteExact.setVars registers values refreshed
    result = none ∧
      WordSemStateFiniteExact.evaluate (.move 1 (registers.zip renamed)) refreshed = (none,prepared) ∧
      WordSemStateFiniteExact.getVars registers prepared = some values ∧
      ssaLocalsRel counter mapOut source.locals prepared.locals ∧
      Flapjack.WordAlloc.wordStateEqRel source prepared ∧
      wordExecutionCost wordOptimizerLocalPrice
        (.seq move (.move 1 (registers.zip renamed))) target ≤
          24 * (((sptToAList (sptUnion first second)).map Prod.fst).length + args.length) ∧
      ∃ targetFirst targetSecond,
        wordSemCutEnvs (Flapjack.WordAlloc.applyNummapsKey (optionLookup mapOut) (first,second))
          prepared.locals = some (targetFirst,targetSecond) ∧
        sptDomain targetFirst = (fun key => ∃ name, sptDomain first name ∧ optionLookup mapOut name = key) ∧
        sptDomain targetSecond = (fun key => ∃ name, sptDomain second name ∧ optionLookup mapOut name = key) ∧
        Flapjack.WordAlloc.strongLocalsRel (optionLookup mapOut) (sptDomain first) sourceFirst targetFirst ∧
        Flapjack.WordAlloc.strongLocalsRel (optionLookup mapOut) (sptDomain second) sourceSecond targetSecond ∧
        (∀ a b, sptDomain sourceFirst a → sptDomain sourceFirst b → optionLookup mapOut a = optionLookup mapOut b → a = b) ∧
        (∀ a b, sptDomain sourceSecond a → sptDomain sourceSecond b → optionLookup mapOut a = optionLookup mapOut b → a = b) ∧
        sptDomain sourceFirst = sptDomain first ∧ sptDomain sourceSecond = sptDomain second := by
  have preparation := returningPrepareArguments source target ssa next args values first second
    sourceFirst sourceSecond cut read related allocated valid frame
  generalize produced : listNextVarRenameMove (width := 64) ssa (next+2)
    ((sptToAList (sptUnion first second)).map Prod.fst) = output at preparation ⊢
  rcases output with ⟨move, mapOut, counter⟩
  dsimp only at preparation ⊢
  generalize evaluated : evaluate move target = run at preparation ⊢
  rcases run with ⟨result, refreshed⟩
  dsimp only at preparation ⊢
  obtain ⟨normal, moveRun, reread, newRelated, newFrame, cuts⟩ := preparation
  refine ⟨normal, moveRun, reread, newRelated, newFrame, ?_, cuts⟩
  have budget := optimizer_seq_budget move
    (.move 1 (((List.range (args.map (optionLookup ssa)).length).map fun key => 2*(key+1)).zip
      (args.map (optionLookup ssa))))
    (24 * ((sptToAList (sptUnion first second)).map Prod.fst).length)
    (24 * args.length) (fun state => ?_) (fun state => ?_) target
  · simpa only [Nat.mul_add] using budget
  · have cost := optimizer_refresh_move_cost ssa (next+2)
      ((sptToAList (sptUnion first second)).map Prod.fst) state
    rw [produced] at cost
    exact Nat.le_of_eq cost
  · simp only [wordExecutionCost, wordOptimizerLocalPrice, List.length_zip,
      List.length_map, List.length_range, Nat.min_self]
    exact Nat.le_refl _

#print axioms returningPrepareArguments_cost
end InitECandidate.Runtime.FineCost
