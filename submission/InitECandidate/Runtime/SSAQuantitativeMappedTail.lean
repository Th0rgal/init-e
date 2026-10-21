import InitECandidate.Runtime.FullSSATableTailCost
import InitECandidate.Runtime.SSAQuantitativeTail
namespace InitECandidate.Runtime.FineCost
open Flapjack Flapjack.Compiler.Backend Flapjack.Compiler.Backend.WordAlloc
open Flapjack.WordSemStateFiniteExact
set_option maxHeartbeats 6000000
set_option pp.structureInstances false

/-- Actual SSA tail-call argument moves followed by a call through the
compiled function table. The static head pays the emitted argument move and
the selected callee's full-SSA entry. The callee IH is strictly clock/depth
guarded; this theorem does not claim the whole global induction is closed. -/
theorem ssa_quantitative_mapped_tail {C F : Type}
    (SP TP : WordLangProgHOL (BitVec 64) → Nat) (seqZero : ∀ a b, TP (.seq a b) = 0)
    (source target : WordSemStateFiniteExact 64 C F) (map : Spt Nat) (next : Nat)
    (destination : Option Nat) (arguments : List Nat)
    (tables : List (Spt Nat × Spt Unit × Spt Unit))
    (frame : FullSSATableFrame source target)
    (related : ssaLocalsRel next map source.locals target.locals)
    (codeFree : WordProps.noInstallCode source.code)
    (fits : ∀ (inputs actualArguments : List (WordLocW 64)) (body : WordLangProgHOL (BitVec 64)) (size : Option Nat),
      wordSemFindCode destination inputs source.code source.stackSize = some (actualArguments,body,size) →
      let setup := setupSSA (outputWidth := 64) actualArguments.length (limitVar body) body;
      ssaCostFits SP TP body setup.2.1 setup.2.2 [])
    (funding : ∀ (inputs actualArguments : List (WordLocW 64)) (body : WordLangProgHOL (BitVec 64)) (size : Option Nat),
      wordSemFindCode destination inputs source.code source.stackSize = some (actualArguments,body,size) →
      let renamed := arguments.map (optionLookup map);
      let registers := (List.range renamed.length).map (fun key => 2*key);
      TP (.move 1 (registers.zip renamed)) + TP (.call none destination registers none) +
          fullSSAEntryPrice TP actualArguments.length body ≤ SP (.call none destination arguments none))
    (ih : FullSSATableFunctionIH (C := C) (F := F) SP TP source.termdep source.clock) :
    ∃ permutation : Nat → Nat → Nat,
      let sourceState := {source with permute := permutation}
      let sourceRun := evaluate (.call none destination arguments none) sourceState
      let targetProgram := (ssaCcTrans (.call none destination arguments none) map next tables).1
      let targetRun := evaluate targetProgram target
      sourceRun.1 = some .error ∨ sourceRun.1 = targetRun.1 ∧
        FullSSATableFrame sourceRun.2 targetRun.2 ∧ sourceRun.2.locals = targetRun.2.locals ∧
        wordExecutionCost (fun p _ => TP p) targetProgram target ≤
          wordExecutionCost (fun p _ => SP p) (.call none destination arguments none) sourceState := by
  classical
  cases read : getVars arguments source with
  | none =>
    refine ⟨source.permute,Or.inl ?_⟩
    simp [WordToWord.evaluate_call_eq,read]
  | some values =>
    let renamed := arguments.map (optionLookup map)
    let registers := (List.range renamed.length).map (fun key => 2*key)
    let moved := setVars registers values target
    have preparation := ssa_tail_arguments source target map next arguments values related read
    have moveRun : evaluate (.move 1 (registers.zip renamed)) target = (none,moved) := preparation.1
    have preparedFrame : FullSSATableFrame source moved := by
      simpa only [moved,setVars,FullSSATableFrame,Flapjack.WordAlloc.wordStateEqRel] using frame
    have argumentRead : ∀ inputs, getVars arguments source = some inputs → getVars registers moved = some inputs := by
      intro inputs actual
      rw [read] at actual
      have equal := Option.some.inj actual
      subst inputs
      exact preparation.2
    have guard : wordSemBadDestArgs destination registers = wordSemBadDestArgs destination arguments :=
      ssa_tail_destination_guard destination arguments map
    obtain ⟨permutation,post⟩ := fullSSATable_tail_cost SP TP (TP (.move 1 (registers.zip renamed)))
      destination arguments registers source moved preparedFrame argumentRead guard codeFree fits funding ih
    have compiledWhole : ssaCcTrans (width := 64) (.call none destination arguments none) map next tables =
        (.seq (.move 1 (registers.zip renamed)) (.call none destination registers none),map,next) := rfl
    have prefixRun : evaluate (.seq (.move 1 (registers.zip renamed)) (.call none destination registers none)) target =
        evaluate (.call none destination registers none) moved :=
      evaluateSeqCollapse _ _ target moved moveRun
    have prefixCost : wordExecutionCost (fun p (_ : WordSemStateFiniteExact 64 C F) => TP p)
        (.seq (.move 1 (registers.zip renamed)) (.call none destination registers none)) target =
        TP (.move 1 (registers.zip renamed)) +
          wordExecutionCost (fun p _ => TP p) (.call none destination registers none) moved := by
      rw [wordExecutionCost_seq,moveRun]
      simp only [seqZero,Nat.zero_add]
      rw [wordExecutionCost_atomic _ (.move 1 (registers.zip renamed)) _ rfl]
    refine ⟨permutation,?_⟩
    dsimp only
    rw [compiledWhole]
    dsimp only
    rw [prefixRun,prefixCost]
    exact post

#print axioms ssa_quantitative_mapped_tail
end InitECandidate.Runtime.FineCost
