import InitECandidate.Runtime.SSAReturningMappedPreparation
import InitECandidate.Runtime.SSAQuantitativeMappedAllowance
namespace InitECandidate.Runtime.FineCost
open Flapjack Flapjack.Compiler.Backend Flapjack.Compiler.Backend.WordAlloc
open Flapjack.WordSemStateFiniteExact
set_option maxHeartbeats 6000000
set_option pp.structureInstances false

/-- Normal or singleton exception continuation over the mapped callee table.
Actual prefix preparation supplies all body-entry invariants; only the genuine
smaller mapped body IH remains. One scheduler witnesses semantics and cost. -/
theorem ssa_returning_mapped_continuation_entry {C F : Type}
    (SP TP : WordLangProgHOL (BitVec 64) → Nat) (bodyEntry : Spt Nat → Nat → Nat)
    (body : WordLangProgHOL (BitVec 64))
    (source target : WordSemStateFiniteExact 64 C F) (ssa : Spt Nat)
    (seqZero : ∀ a b, TP (.seq a b) = 0)
    (names : Spt Unit) (counter : Nat) (returns : List Nat) (values : List (WordLocW 64))
    (tables : List (Spt Nat × Spt Unit × Spt Unit))
    (retMove : WordLangProgHOL (BitVec 64)) (moveMap : Spt Nat) (moveNext bindNext : Nat)
    (renamed : List Nat) (retMap : Spt Nat) (retNext : Nat)
    (compiled : WordLangProgHOL (BitVec 64)) (finalMap : Spt Nat) (finalNext : Nat)
    (moveProduced : listNextVarRenameMove (width := 64) (sptInter ssa names) (counter+2)
      ((sptToAList names).map Prod.fst) = (retMove,moveMap,moveNext))
    (renameProduced : listNextVarRename returns moveMap bindNext = (renamed,retMap,retNext))
    (bodyProduced : ssaCcTrans body retMap retNext tables = (compiled,finalMap,finalNext))
    (bindingIncrease : moveNext ≤ bindNext) (bindingClass : isAllocVar bindNext)
    (related : ssaLocalsRel counter (sptInter ssa names) source.locals target.locals)
    (valid : ssaMapOK counter ssa) (stackClass : isStackVar counter)
    (sourceDomain : sptDomain source.locals = sptDomain names)
    (lengths : returns.length = values.length) (distinct : returns.Nodup)
    (below : ∀ name ∈ returns, name < counter)
    (bodyBounds : everyVarHOL (fun key => decide (key < counter)) body = true)
    (frame : FullSSATableFrame source target) (tableValid : ltOK tables)
    (codeFree : WordProps.noInstallCode source.code)
    (bodyIH : SSAMappedBodyAllowance (C := C) (F := F) SP TP body retMap retNext tables
      (bodyEntry retMap retNext)) :
    let registers := (List.range returns.length).map (fun index => 2*(index+1))
    let prepared := setVars registers values target
    ∃ permutation : Nat → Nat → Nat,
      let sourceState := {setVars returns values source with permute := permutation}
      let sourceRun := evaluate body sourceState
      let targetRun := evaluate (.seq retMove (.seq (.move 1 (renamed.zip registers)) compiled)) prepared
      sourceRun.1 = some .error ∨
        sourceRun.1 = targetRun.1 ∧ FullSSATableFrame sourceRun.2 targetRun.2 ∧
        SSAResultLocals finalNext finalMap tables sourceRun.2.locals targetRun.2.locals sourceRun.1 ∧
        wordExecutionCost (fun p _ => TP p)
          (.seq retMove (.seq (.move 1 (renamed.zip registers)) compiled)) prepared ≤
          TP retMove + TP (.move 1 (renamed.zip registers)) + bodyEntry retMap retNext +
            wordExecutionCost (fun p _ => SP p) body sourceState := by
  let registers := (List.range returns.length).map (fun index => 2*(index+1))
  obtain ⟨after,refreshed,moveRun,copyRun,prefixRun,afterFrame,afterRelated,afterAllocated,afterValid,increase,prefixCost⟩ :=
    ssa_returning_mapped_preparation TP seqZero source target ssa names counter returns values
      retMove moveMap moveNext bindNext renamed retMap retNext moveProduced renameProduced
      bindingIncrease bindingClass related valid stackClass sourceDomain lengths distinct below frame
  have finalBounds : everyVarHOL (fun key => decide (key < retNext)) body = true :=
    Flapjack.everyVarMono _ body _ ⟨fun key bound => by
      simp only [decide_eq_true_eq] at bound ⊢
      exact Nat.lt_of_lt_of_le bound increase,bodyBounds⟩
  obtain ⟨permutation,post⟩ := bodyIH (setVars returns values source) after
    ⟨afterFrame,afterRelated,afterAllocated,finalBounds,afterValid,tableValid⟩ codeFree
  refine ⟨permutation,?_⟩
  dsimp only at post ⊢
  rw [bodyProduced] at post
  have actual : evaluate (.seq retMove (.seq (.move 1 (renamed.zip registers)) compiled))
      (setVars registers values target) = evaluate compiled after := by
    rw [evaluateSeqCollapse _ _ _ _ moveRun,evaluateSeqCollapse _ _ _ _ copyRun]
  rw [actual]
  rcases post with error | ⟨same,postFrame,postLocals,bodyCost⟩
  · exact Or.inl error
  · right
    refine ⟨same,postFrame,postLocals,?_⟩
    have atomic : wordCostAtomic retMove = true := by
      have shape := congrArg Prod.fst moveProduced
      simp only [listNextVarRenameMove] at shape
      rw [←shape]
      rfl
    rw [wordExecutionCost_seq,moveRun]
    simp only [seqZero,Nat.zero_add]
    rw [wordExecutionCost_seq,copyRun]
    simp only [seqZero,Nat.zero_add]
    rw [wordExecutionCost_atomic _ retMove _ atomic,
      wordExecutionCost_atomic _ (.move 1 (renamed.zip registers)) _ rfl]
    dsimp only [registers] at bodyCost ⊢
    omega

#print axioms ssa_returning_mapped_continuation_entry
end InitECandidate.Runtime.FineCost
