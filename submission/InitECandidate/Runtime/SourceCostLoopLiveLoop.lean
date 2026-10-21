import InitECandidate.Runtime.SourceCostLoopLiveLoopPlan
namespace InitECandidate.Runtime.FineCost
open Flapjack Flapjack.LoopSemStateFiniteExact

private theorem loop_live_plan_entry {F : Type}
    {contexts : List (NumSet × NumSet)} {liveIn liveOut wanted : NumSet} {body : HolLoopProg 64}
    (plan : LoopLivePlan contexts liveIn liveOut body wanted)
    (s entry : LoopSemStateFiniteExact 64 F) (locals : Spt (WordLocW 64))
    (cut : cutRes liveIn (none, s) = (none, entry))
    (input : sptSubspt (sptInter s.locals plan.header) locals) :
    ∃ entryLocals,
      cutRes plan.header (none, { s with locals := locals }) = (none, { entry with locals := entryLocals }) ∧
      sptSubspt (sptInter entry.locals plan.bodyLive) entryLocals := by
  obtain ⟨entryLocals, targetCut, footprint⟩ := live_projection_cut s locals liveIn plan.header
    plan.bodyLive input plan.headerInside plan.bodyNeeds (by rw [cut]; simp)
  rw [cut] at targetCut footprint
  exact ⟨entryLocals, targetCut, footprint⟩

/-- Every continuing iteration pays for exactly its pruned body and reached
recursive loop. The same compiler plan is used at both runtime states. -/
theorem loop_live_paid_loop_next {F : Type}
    {s entry middle : LoopSemStateFiniteExact 64 F} {liveIn liveOut : NumSet} {body : HolLoopProg 64}
    {result : Option (LoopResultExact 64)} {output} {wb wr : Nat}
    (cut : cutRes liveIn (none, s) = (none, entry))
    (again : result = none ∨ result = some (.continue 0))
    (one : LoopLivePaid entry body (result, middle) wb)
    (rest : LoopLivePaid middle (.loop liveIn body liveOut) output wr) :
    LoopLivePaid s (.loop liveIn body liveOut) output (16 + wb + wr) := by
  intro contexts locals wanted input
  obtain ⟨plan⟩ := loop_live_plan contexts liveIn liveOut body wanted
  have headerInput : sptSubspt (sptInter s.locals plan.header) locals := by
    simpa only [plan.compiled] using input
  obtain ⟨entryLocals, targetCut, bodyFootprint⟩ := loop_live_plan_entry plan s entry locals cut headerInput
  have bodyInput : sptSubspt (sptInter entry.locals
      (shrinkHOL ((plan.header, plan.breakLive) :: contexts) body
        (sptUnion liveIn (sptInter liveOut wanted))).2) entryLocals := by
    simpa only [plan.bodyCompiled] using bodyFootprint
  obtain ⟨middleLocals, wb', bodyRun, bodyBound, bodyRelated⟩ :=
    one ((plan.header, plan.breakLive) :: contexts) entryLocals
      (sptUnion liveIn (sptInter liveOut wanted)) bodyInput
  have middleFootprint : sptSubspt (sptInter middle.locals plan.header) middleLocals := by
    rcases again with rfl | rfl
    · apply live_projection_weaken bodyRelated
      intro key member
      exact (sptMem_sptUnion _ _ key).mpr (Or.inl (plan.headerInside key member))
    · simpa only [liveLocalsAfter, sptOel] using bodyRelated
  have restInput : sptSubspt (sptInter middle.locals
      (shrinkHOL contexts (.loop liveIn body liveOut) wanted).2) middleLocals := by
    simpa only [plan.compiled] using middleFootprint
  obtain ⟨postLocals, wr', restRun, restBound, postRelated⟩ := rest contexts middleLocals wanted restInput
  rw [plan.bodyCompiled] at bodyRun
  rw [plan.compiled] at restRun
  refine ⟨postLocals, 16 + wb' + wr', ?_, by omega, postRelated⟩
  simpa only [plan.compiled] using LoopWork.loopNext targetCut bodyRun again restRun

/-- A Break-0 iteration does not execute another body. Semantic correctness
supplies the exact final pruned cut-state; its work is one loop entry plus the
actual body work. -/
theorem loop_live_paid_loop_break {F : Type}
    {s entry middle : LoopSemStateFiniteExact 64 F} {liveIn liveOut : NumSet} {body : HolLoopProg 64}
    {wb : Nat} (cut : cutRes liveIn (none, s) = (none, entry))
    (bodyRun : LoopWork entry body (some (.break 0), middle) wb)
    (bodyPaid : LoopLivePaid entry body (some (.break 0), middle) wb)
    (nonerror : (cutRes liveOut (none, middle)).1 ≠ some .error) :
    LoopLivePaid s (.loop liveIn body liveOut) (cutRes liveOut (none, middle)) (16 + wb) := by
  intro contexts locals wanted input
  obtain ⟨plan⟩ := loop_live_plan contexts liveIn liveOut body wanted
  have headerInput : sptSubspt (sptInter s.locals plan.header) locals := by
    simpa only [plan.compiled] using input
  obtain ⟨entryLocals, targetCut, bodyFootprint⟩ := loop_live_plan_entry plan s entry locals cut headerInput
  have bodyInput : sptSubspt (sptInter entry.locals
      (shrinkHOL ((plan.header, plan.breakLive) :: contexts) body
        (sptUnion liveIn (sptInter liveOut wanted))).2) entryLocals := by
    simpa only [plan.bodyCompiled] using bodyFootprint
  obtain ⟨middleLocals, wb', targetBody, bound, related⟩ := bodyPaid
    ((plan.header, plan.breakLive) :: contexts) entryLocals
      (sptUnion liveIn (sptInter liveOut wanted)) bodyInput
  rw [plan.bodyCompiled] at targetBody
  have target := LoopWork.loopBreak (liveOut := sptInter liveOut wanted) targetCut targetBody
  have target' : LoopWork { s with locals := locals }
      (shrinkHOL contexts (.loop liveIn body liveOut) wanted).1
      (cutRes (sptInter liveOut wanted) (none, { middle with locals := middleLocals })) (16 + wb') := by
    simpa only [plan.compiled] using target
  have source : LoopWork s (.loop liveIn body liveOut)
      ((cutRes liveOut (none, middle)).1, (cutRes liveOut (none, middle)).2) (16 + wb) :=
    LoopWork.loopBreak cut bodyRun
  exact loop_live_finish source nonerror contexts locals wanted input target' (by omega)

/-- Propagated exits retain the source result and charge no recursive loop. -/
theorem loop_live_paid_loop_exit {F : Type}
    {s entry middle : LoopSemStateFiniteExact 64 F} {liveIn liveOut : NumSet} {body : HolLoopProg 64}
    {result : Option (LoopResultExact 64)} {wb : Nat}
    (cut : cutRes liveIn (none, s) = (none, entry))
    (bodyRun : LoopWork entry body (result, middle) wb)
    (stop : result ≠ none ∧ result ≠ some (.continue 0) ∧ result ≠ some (.break 0))
    (bodyPaid : LoopLivePaid entry body (result, middle) wb)
    (nonerror : exitLoop result ≠ some .error) :
    LoopLivePaid s (.loop liveIn body liveOut) (exitLoop result, middle) (16 + wb) := by
  intro contexts locals wanted input
  obtain ⟨plan⟩ := loop_live_plan contexts liveIn liveOut body wanted
  have headerInput : sptSubspt (sptInter s.locals plan.header) locals := by
    simpa only [plan.compiled] using input
  obtain ⟨entryLocals, targetCut, bodyFootprint⟩ := loop_live_plan_entry plan s entry locals cut headerInput
  have bodyInput : sptSubspt (sptInter entry.locals
      (shrinkHOL ((plan.header, plan.breakLive) :: contexts) body
        (sptUnion liveIn (sptInter liveOut wanted))).2) entryLocals := by
    simpa only [plan.bodyCompiled] using bodyFootprint
  obtain ⟨middleLocals, wb', targetBody, bound, related⟩ := bodyPaid
    ((plan.header, plan.breakLive) :: contexts) entryLocals
      (sptUnion liveIn (sptInter liveOut wanted)) bodyInput
  rw [plan.bodyCompiled] at targetBody
  have target := LoopWork.loopExit (liveOut := sptInter liveOut wanted) targetCut targetBody stop
  have target' : LoopWork { s with locals := locals }
      (shrinkHOL contexts (.loop liveIn body liveOut) wanted).1
      (exitLoop result, { middle with locals := middleLocals }) (16 + wb') := by
    simpa only [plan.compiled] using target
  exact loop_live_finish (LoopWork.loopExit cut bodyRun stop) nonerror contexts locals wanted
    input target' (by omega)

/-- A loop stopped by its entry cut executes no body and keeps its unit work. -/
theorem loop_live_paid_loop_cut {F : Type}
    {s post : LoopSemStateFiniteExact 64 F} {liveIn liveOut : NumSet} {body : HolLoopProg 64}
    {result : LoopResultExact 64} (stopped : cutRes liveIn (none, s) = (some result, post))
    (nonerror : some result ≠ some .error) :
    LoopLivePaid s (.loop liveIn body liveOut) (some result, post) 16 := by
  intro contexts locals wanted input
  obtain ⟨plan⟩ := loop_live_plan contexts liveIn liveOut body wanted
  have headerInput : sptSubspt (sptInter s.locals plan.header) locals := by
    simpa only [plan.compiled] using input
  obtain ⟨targetLocals, targetCut, _⟩ := live_projection_cut s locals liveIn plan.header .ln
    headerInput plan.headerInside (by intro key impossible; simp [sptMem, sptDomain, sptLookup] at impossible)
    (by simpa only [stopped] using nonerror)
  rw [stopped] at targetCut
  have target := LoopWork.loopCut (body := plan.bodyCode) (liveOut := sptInter liveOut wanted) targetCut
  have target' : LoopWork { s with locals := locals }
      (shrinkHOL contexts (.loop liveIn body liveOut) wanted).1
      (some result, { post with locals := targetLocals }) 16 := by
    simpa only [plan.compiled] using target
  exact loop_live_finish (LoopWork.loopCut (body := body) (liveOut := liveOut) stopped)
    nonerror contexts locals wanted input target' (Nat.le_refl _)

#print axioms loop_live_paid_loop_next
#print axioms loop_live_paid_loop_break
#print axioms loop_live_paid_loop_exit
#print axioms loop_live_paid_loop_cut
end InitECandidate.Runtime.FineCost
