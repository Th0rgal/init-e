import InitECandidate.Runtime.MptInsertNullStop
import InitECandidate.Runtime.RankedWhile
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

def mptInsertCondition : ExpHOL 64 :=
 .cmp .notEqual (.var .local (ofString "go")) (.const 0)

private def EmptyRank {F : Type} (s : PanSemStateFiniteExact 64 F) (n : Nat) : Prop :=
 (n=0 ∧ s.locals.lookup (ofString "go")=some (.val (.word (0#64)))) ∨
 (n=1 ∧ s.locals.lookup (ofString "node")=some (.val (.word (0#64))))

/-- The actual insertion loop from a null node needs at most one iteration.
Its bound includes the actual leaf call and every rejection outcome. -/
theorem mpt_insert_empty_loop_bounded {F : Type} (s : PanSemStateFiniteExact 64 F)
 (node : s.locals.lookup (ofString "node")=some (.val (.word (0#64))))
 (code : s.code=originalRuntimeCode) (budget : 4≤s.clock) :
 RunBounded s (.while mptInsertCondition mptInsertLoopStep) 4 := by
 have exit : ∀{F : Type}(state : PanSemStateFiniteExact 64 F),EmptyRank state 0→∀w : BitVec 64,
  evalHOLFinite state (h:=fun a=>Classical.propDecidable (state.memaddrs a)) mptInsertCondition=
   some (.val (.word w))→w=0 := by
  intro F state rank w guard
  rcases rank with ⟨_,atGo⟩|⟨impossible,_⟩
  · rw [evalHOLFinite_eq_toExact] at guard
    simpa [mptInsertCondition,evalHOLExact,atGo,Compiler.Encoders.Asm.wordCmpHOL] using guard.symm
  · omega
 have step : ∀{F : Type}(state : PanSemStateFiniteExact 64 F)(n : Nat)(w : BitVec 64),
  state.code=originalRuntimeCode→EmptyRank state (n+1)→
  evalHOLFinite state (h:=fun a=>Classical.propDecidable (state.memaddrs a)) mptInsertCondition=
   some (.val (.word w))→w≠0→3+1≤state.clock→
  state.clock-1≤(evaluateHOLFiniteState (decClockHOLFinite state) mptInsertLoopStep).2.clock+3 ∧
  (evaluateHOLFiniteState (decClockHOLFinite state) mptInsertLoopStep).2.clock≤state.clock-1 ∧
  (evaluateHOLFiniteState (decClockHOLFinite state) mptInsertLoopStep).1≠some .timeOut ∧
  ((evaluateHOLFiniteState (decClockHOLFinite state) mptInsertLoopStep).1=none ∨
   (evaluateHOLFiniteState (decClockHOLFinite state) mptInsertLoopStep).1=some .continue→
   ∃m,m≤n ∧ EmptyRank (evaluateHOLFiniteState (decClockHOLFinite state) mptInsertLoopStep).2 m ∧
    (evaluateHOLFiniteState (decClockHOLFinite state) mptInsertLoopStep).2.code=state.code) ∧
  ((evaluateHOLFiniteState (decClockHOLFinite state) mptInsertLoopStep).1=some .break→False ∧
   ∃m,EmptyRank (evaluateHOLFiniteState (decClockHOLFinite state) mptInsertLoopStep).2 m ∧
    (evaluateHOLFiniteState (decClockHOLFinite state) mptInsertLoopStep).2.code=state.code) := by
  intro F state n w installed rank _ _ clock
  have atNode : state.locals.lookup (ofString "node")=some (.val (.word (0#64))) := by
   rcases rank with ⟨impossible,_⟩|⟨_,binding⟩
   · omega
   · exact binding
  have bounded:=mpt_insert_null_step_bounded (decClockHOLFinite state) atNode installed (by change 3≤state.clock-1;omega)
  refine ⟨bounded.1,bounded.2.1,bounded.2.2,?_,?_⟩
  · intro flowing
    rcases flowing with normal|continued
    · cases run : evaluateHOLFiniteState (decClockHOLFinite state) mptInsertLoopStep with
      | mk result post =>
       rw [run] at normal
       dsimp only at normal
       subst result
       have stopped:=mpt_insert_null_step_stops (decClockHOLFinite state) post atNode run
       have metadata:=evaluateHOLFiniteState_metadata (decClockHOLFinite state) mptInsertLoopStep
       rw [run] at metadata
       exact ⟨0,Nat.zero_le _,Or.inl ⟨rfl,stopped⟩,metadata.1⟩
    · exact False.elim (mpt_insert_null_step_no_continue (decClockHOLFinite state) atNode continued)
  · intro broken
    exact False.elim (mpt_insert_null_step_no_break (decClockHOLFinite state) atNode broken)
 have bounded:=rankedWhile_run mptInsertCondition mptInsertLoopStep 3 EmptyRank False exit step
  1 s code (Or.inr ⟨rfl,node⟩) budget
 exact ⟨bounded.1,bounded.2.1,bounded.2.2.1⟩

theorem source_mptInsert_body : sourceFunctionBody Guest.guestFn__mpt_insert_node=
 .dec (ofString "result") .one (.const 0)
  (.dec (ofString "slot") .one (.const 0)
   (.dec (ofString "go") .one (.const 1)
    (.seq (.while mptInsertCondition mptInsertLoopStep) (.return (.var .local (ofString "result")))))) := by
 simp only [sourceFunctionBody,mptInsertCondition,mptInsertLoopStep,
  InitECandidate.Proofs.FrontendCodecComputation.declToHOL_eq]
 rfl

/-- The entire original insertion body on an empty root is bounded, without
any assumptions on input memory, allocation room or successful callees. -/
theorem mpt_insert_empty_body_bounded {F : Type} (s : PanSemStateFiniteExact 64 F)
 (node : s.locals.lookup (ofString "node")=some (.val (.word (0#64))))
 (code : s.code=originalRuntimeCode) (budget : 4≤s.clock) :
 RunBounded s (sourceFunctionBody Guest.guestFn__mpt_insert_node) 4 := by
 rw [source_mptInsert_body]
 apply RunBounded.decConst
 apply RunBounded.decConst
 apply RunBounded.decConst
 refine RunBounded.seq (a:=4) (b:=0) ?_ (by exact budget) ?_
 · apply mpt_insert_empty_loop_bounded
   · simpa (config:={decide:=true}) [setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE] using node
   · exact code
   · exact budget
 · intro next _ nextCode _
   exact ProgBounded.straight _ rfl next (nextCode.trans code) (Nat.zero_le _)

#print axioms mpt_insert_empty_loop_bounded
#print axioms mpt_insert_empty_body_bounded
end InitECandidate.Runtime
