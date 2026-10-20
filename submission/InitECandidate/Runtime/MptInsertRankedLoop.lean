import InitECandidate.Runtime.MptInsertLoopInvariant
import InitECandidate.Runtime.MptInsertEmptyBound
import InitECandidate.Runtime.NoTopBreak
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

def MptInsertRank {F : Type} (live extensions branches : Set (BitVec 64)) (size : BitVec 64 → Nat)
 (frontier key length valuePointer valueLength : BitVec 64) (s : PanSemStateFiniteExact 64 F) (rank : Nat) : Prop :=
 (rank=0 ∧s.locals.lookup (ofString "go")=some (.val (.word (0#64)))) ∨
 MptInsertActive s live extensions branches size frontier key length valuePointer valueLength rank

theorem mpt_insert_step_no_continue {F : Type} (s : PanSemStateFiniteExact 64 F) :
 (evaluateHOLFiniteState s mptInsertLoopStep).1≠some .continue := by
 apply evaluate_noTopContinue
 simp only [mptInsertLoopStep,sourceFunctionBody,Proofs.FrontendCodecComputation.declToHOL_eq]
 decide

theorem mpt_insert_step_no_break {F : Type} (s : PanSemStateFiniteExact 64 F) :
 (evaluateHOLFiniteState s mptInsertLoopStep).1≠some .break := by
 apply evaluate_noTopBreak
 simp only [mptInsertLoopStep,sourceFunctionBody,Proofs.FrontendCodecComputation.declToHOL_eq]
 decide

/-- The actual indexed insertion while loop is bounded by its concrete
remaining-key rank, including failures in every body call and memory access.
Only continuing normal outcomes need preserve the concrete trie world. -/
theorem mpt_insert_ranked_loop_bounded {F : Type} (s : PanSemStateFiniteExact 64 F)
 (live extensions branches : Set (BitVec 64)) (size : BitVec 64 → Nat)
 (frontier key length valuePointer valueLength : BitVec 64) (rank : Nat)
 (active : MptInsertActive s live extensions branches size frontier key length valuePointer valueLength rank)
 (capacity : ∀node∈live,32≤size node) (recordsBefore : ∀node∈live,node.toNat+32≤key.toNat)
 (aligned : key.toNat%8=0) (keyExtent : key.toNat+length.toNat≤33806089496) (short : length.toNat≤18)
 (code : s.code=originalRuntimeCode) (budget : rank*((2^64+203)+1)≤s.clock) :
 RunBounded s (.while mptInsertCondition mptInsertLoopStep) (rank*((2^64+203)+1)) := by
 let Rank : ∀{F : Type},PanSemStateFiniteExact 64 F→Nat→Prop:=
  fun {F} state n=>MptInsertRank live extensions branches size frontier key length valuePointer valueLength state n
 have exit : ∀{F : Type}(state : PanSemStateFiniteExact 64 F),Rank state 0→∀w : BitVec 64,
  evalHOLFinite state (h:=fun a=>Classical.propDecidable (state.memaddrs a)) mptInsertCondition=some (.val (.word w))→w=0 := by
  intro F state ranked w guard
  rcases ranked with ⟨_,atGo⟩|next
  · rw [evalHOLFinite_eq_toExact] at guard
    simpa [mptInsertCondition,evalHOLExact,atGo,Compiler.Encoders.Asm.wordCmpHOL] using guard.symm
  · obtain ⟨node,slot,level,root,a,b,c,d,e,f,g,h,inside,rankEq⟩:=next.path
    omega
 have step : ∀{F : Type}(state : PanSemStateFiniteExact 64 F)(n : Nat)(w : BitVec 64),
  state.code=originalRuntimeCode→Rank state (n+1)→
  evalHOLFinite state (h:=fun a=>Classical.propDecidable (state.memaddrs a)) mptInsertCondition=some (.val (.word w))→
  w≠0→(2^64+203)+1≤state.clock→
  state.clock-1≤(evaluateHOLFiniteState (decClockHOLFinite state) mptInsertLoopStep).2.clock+(2^64+203) ∧
  (evaluateHOLFiniteState (decClockHOLFinite state) mptInsertLoopStep).2.clock≤state.clock-1 ∧
  (evaluateHOLFiniteState (decClockHOLFinite state) mptInsertLoopStep).1≠some .timeOut ∧
  ((evaluateHOLFiniteState (decClockHOLFinite state) mptInsertLoopStep).1=none ∨
   (evaluateHOLFiniteState (decClockHOLFinite state) mptInsertLoopStep).1=some .continue→
   ∃m,m≤n ∧Rank (evaluateHOLFiniteState (decClockHOLFinite state) mptInsertLoopStep).2 m ∧
    (evaluateHOLFiniteState (decClockHOLFinite state) mptInsertLoopStep).2.code=state.code) ∧
  ((evaluateHOLFiniteState (decClockHOLFinite state) mptInsertLoopStep).1=some .break→False ∧
   ∃m,Rank (evaluateHOLFiniteState (decClockHOLFinite state) mptInsertLoopStep).2 m ∧
    (evaluateHOLFiniteState (decClockHOLFinite state) mptInsertLoopStep).2.code=state.code) := by
  intro F state n w installed ranked guard nonzero clock
  have current : MptInsertActive state live extensions branches size frontier key length valuePointer valueLength (n+1) := by
   rcases ranked with ⟨impossible,_⟩|current
   · omega
   · exact current
  have bounded:=mpt_insert_step_bounded (decClockHOLFinite state) (current.decClock.inputs short) installed (by change 2^64+203≤state.clock-1;omega)
  refine ⟨bounded.1,bounded.2.1,bounded.2.2,?_,?_⟩
  · intro flowing
    rcases flowing with normal|continued
    · cases run : evaluateHOLFiniteState (decClockHOLFinite state) mptInsertLoopStep with
      | mk result post=>
       rw [run] at normal
       dsimp only at normal
       subst result
       have metadata:=evaluateHOLFiniteState_metadata (decClockHOLFinite state) mptInsertLoopStep
       rw [run] at metadata
       by_cases stopped : post.locals.lookup (ofString "go")=some (.val (.word (0#64)))
       · exact ⟨0,Nat.zero_le _,Or.inl ⟨rfl,stopped⟩,metadata.1⟩
       · obtain ⟨nextRank,smaller,nextActive⟩:=mpt_insert_active_step (decClockHOLFinite state) post live extensions branches size frontier key length valuePointer valueLength (n+1)
          current.decClock capacity recordsBefore aligned keyExtent short installed (by change 21≤state.clock-1;omega) stopped run
         exact ⟨nextRank,by omega,Or.inr nextActive,metadata.1⟩
    · exact False.elim (mpt_insert_step_no_continue (decClockHOLFinite state) continued)
  · intro broken
    exact False.elim (mpt_insert_step_no_break (decClockHOLFinite state) broken)
 have bounded:=rankedWhile_run mptInsertCondition mptInsertLoopStep (2^64+203) Rank False exit step rank s code (Or.inr active) budget
 exact ⟨bounded.1,bounded.2.1,bounded.2.2.1⟩

/-- At most eighteen strict nibble advances and one terminal iteration bound
this real indexed trie insertion loop by nineteen whole body budgets. -/
theorem mpt_insert_indexed_loop_bounded {F : Type} (s : PanSemStateFiniteExact 64 F)
 (live extensions branches : Set (BitVec 64)) (size : BitVec 64 → Nat)
 (frontier key length valuePointer valueLength : BitVec 64) (rank : Nat)
 (active : MptInsertActive s live extensions branches size frontier key length valuePointer valueLength rank)
 (capacity : ∀node∈live,32≤size node) (recordsBefore : ∀node∈live,node.toNat+32≤key.toNat)
 (aligned : key.toNat%8=0) (keyExtent : key.toNat+length.toNat≤33806089496) (short : length.toNat≤18)
 (code : s.code=originalRuntimeCode) (budget : 19*((2^64+203)+1)≤s.clock) :
 RunBounded s (.while mptInsertCondition mptInsertLoopStep) (19*((2^64+203)+1)) := by
 obtain ⟨node,slot,level,root,a,b,c,d,e,f,g,h,inside,rankEq⟩:=active.path
 have rankBound : rank≤19:=by omega
 have costBound:=Nat.mul_le_mul_right ((2^64+203)+1) rankBound
 have enough : rank*((2^64+203)+1)≤s.clock:=costBound.trans budget
 have bounded : RunBounded s (.while mptInsertCondition mptInsertLoopStep) (rank*((2^64+203)+1)) :=
  mpt_insert_ranked_loop_bounded s live extensions branches size frontier key length valuePointer valueLength rank active
   capacity recordsBefore aligned keyExtent short code enough
 exact RunBounded.weaken bounded costBound

#print axioms mpt_insert_step_no_continue
#print axioms mpt_insert_step_no_break
#print axioms mpt_insert_indexed_loop_bounded
end InitECandidate.Runtime
