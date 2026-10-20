import InitECandidate.Runtime.SourceCostLoopLiveGeometry
namespace InitECandidate.Runtime.FineCost
open Flapjack Flapjack.LoopSemStateFiniteExact

/-- The conditional charges only its selected branch. Input projection supplies
both compared words and the selected branch's live footprint. Existing exact
semantic correctness identifies the final cut-state without repricing it. -/
theorem loop_live_paid_ite {F : Type} {s : LoopSemStateFiniteExact 64 F}
    {operator : Cmp} {register : Nat} {right : RegImm (BitVec 64)}
    {yes no : HolLoopProg 64} {liveOut : NumSet} {x y : BitVec 64}
    {output : Option (LoopResultExact 64) × LoopSemStateFiniteExact 64 F} {w : Nat}
    (lhs : sptLookup register s.locals = some (.word x))
    (rhs : LoopSemStateFiniteExact.getVarImm right s = some (.word y))
    (branch : LoopWork s (if Compiler.Encoders.Asm.wordCmpHOL operator x y then yes else no)
      output w)
    (paid : LoopLivePaid s (if Compiler.Encoders.Asm.wordCmpHOL operator x y then yes else no)
      output w)
    (nonerror : (cutRes liveOut output).1 ≠ some .error) :
    LoopLivePaid s (.ite operator register right yes no liveOut) (cutRes liveOut output) (2 + w) := by
  intro contexts locals live input
  rcases compiledYes : shrinkHOL contexts yes (sptInter live liveOut) with ⟨yes', yesLive⟩
  rcases compiledNo : shrinkHOL contexts no (sptInter live liveOut) with ⟨no', noLive⟩
  let wide := sptInsert register () (sptUnion (regImmLive right) (sptUnion yesLive noLive))
  have compiled : shrinkHOL contexts (.ite operator register right yes no liveOut) live =
      (.ite operator register right yes' no' (sptInter live liveOut), wide) := by
    cases right <;> simp only [shrinkHOL, compiledYes, compiledNo, regImmLive, wide]
  have projected : sptSubspt (sptInter s.locals wide) locals := by
    simpa only [compiled] using input
  have insertSelf : ∀ key (tree : NumSet), sptMem key (sptInsert key () tree) := by
    intro key tree
    exact (sptMem_sptInsert key key () tree).mpr (Or.inl rfl)
  have insertKeep : ∀ key other (tree : NumSet), sptMem key tree → sptMem key (sptInsert other () tree) := by
    intro key other tree member
    exact (sptMem_sptInsert key other () tree).mpr (Or.inr member)
  have lhs' : sptLookup register locals = some (.word x) :=
    live_projection_lookup projected (insertSelf register _) lhs
  have rhs' : LoopSemStateFiniteExact.getVarImm right { s with locals := locals } = some (.word y) := by
    cases right with
    | imm value => exact rhs
    | reg key =>
      apply live_projection_lookup projected ?_ rhs
      apply insertKeep
      apply (sptMem_sptUnion _ _ key).mpr
      exact Or.inl (insertSelf key .ln)
  have branchInput : sptSubspt (sptInter s.locals
      (shrinkHOL contexts (if Compiler.Encoders.Asm.wordCmpHOL operator x y then yes else no)
        (sptInter live liveOut)).2) locals := by
    split
    · rw [compiledYes]
      apply live_projection_weaken projected
      intro key member
      apply insertKeep
      apply (sptMem_sptUnion _ _ key).mpr
      apply Or.inr
      exact (sptMem_sptUnion _ _ key).mpr (Or.inl member)
    · rw [compiledNo]
      apply live_projection_weaken projected
      intro key member
      apply insertKeep
      apply (sptMem_sptUnion _ _ key).mpr
      apply Or.inr
      exact (sptMem_sptUnion _ _ key).mpr (Or.inr member)
  obtain ⟨branchLocals, w', branchRun, bound, branchRelated⟩ :=
    paid contexts locals (sptInter live liveOut) branchInput
  have branchRun' : LoopWork { s with locals := locals }
      (if Compiler.Encoders.Asm.wordCmpHOL operator x y then yes' else no')
      (output.1, { output.2 with locals := branchLocals }) w' := by
    split <;> simpa only [*, Bool.false_eq_true, ↓reduceIte, compiledYes, compiledNo] using branchRun
  have target := LoopWork.iteBranch (live := sptInter live liveOut) lhs' rhs' branchRun'
  have target' : LoopWork { s with locals := locals }
      (shrinkHOL contexts (.ite operator register right yes no liveOut) live).1
      (cutRes (sptInter live liveOut) (output.1, { output.2 with locals := branchLocals }))
      (2 + w') := by
    simpa only [compiled] using target
  have source : LoopWork s (.ite operator register right yes no liveOut)
      ((cutRes liveOut output).1, (cutRes liveOut output).2) (2 + w) :=
    LoopWork.iteBranch lhs rhs branch
  exact loop_live_finish source nonerror contexts locals live input target' (by omega)

#print axioms loop_live_paid_ite
end InitECandidate.Runtime.FineCost
