import InitECandidate.Runtime.MptInsertPathsActiveStopped
import InitECandidate.Runtime.MptInsertRankedLoop
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

/-- A normal insertion exit retains its committed root and actual enlarged
allocated world, stored paths and remaining input path. -/
def MptInsertTerminalPaths {F : Type} (s : PanSemStateFiniteExact 64 F)
 (live extensions branches : Set (BitVec 64)) (key length : BitVec 64) : Prop :=
 ∃root : BitVec 64,∃larger newExtensions newBranches : Set (BitVec 64),∃newSize : BitVec 64→Nat,∃finish : BitVec 64,
 s.locals.lookup (ofString "result")=some (.val (.word root)) ∧(root=0 ∨root∈larger) ∧
 live⊆larger ∧extensions⊆newExtensions ∧branches⊆newBranches ∧
 AllocatedTrieWorld s larger newExtensions newBranches newSize finish ∧
 TrieNodeKinds s larger newExtensions newBranches ∧TrieNodePaths s larger newExtensions newBranches newSize finish ∧
 TriePathBuffer s larger newSize key length finish

def MptInsertPathsRank {F : Type} (live extensions branches : Set (BitVec 64)) (size : BitVec 64→Nat)
 (frontier key length valuePointer valueLength : BitVec 64) (s : PanSemStateFiniteExact 64 F) (rank : Nat) : Prop :=
 (rank=0 ∧s.locals.lookup (ofString "go")=some (.val (.word (0#64))) ∧
  MptInsertTerminalPaths s live extensions branches key length) ∨
 MptInsertPathsActive s live extensions branches size frontier key length valuePointer valueLength rank

/-- The actual ranked loop retains its terminal world and the explicit
source-clock bound, including every exceptional or rejecting body outcome. -/
theorem mpt_insert_ranked_loop_paths {F : Type} (s : PanSemStateFiniteExact 64 F)
 (live extensions branches : Set (BitVec 64)) (size : BitVec 64 → Nat)
 (frontier key length valuePointer valueLength : BitVec 64) (rank : Nat)
 (active : MptInsertPathsActive s live extensions branches size frontier key length valuePointer valueLength rank)
 (capacity : ∀node∈live,32≤size node) (recordsBefore : ∀node∈live,node.toNat+32≤key.toNat)
 (aligned : key.toNat%8=0) (keyExtent : key.toNat+length.toNat≤33806089496) (short : length.toNat≤18)
 (code : s.code=originalRuntimeCode) (budget : rank*((2^64+203)+1)≤s.clock) :
 RankedOutcome s mptInsertCondition (rank*((2^64+203)+1))
  (fun {F} state n=>MptInsertPathsRank live extensions branches size frontier key length valuePointer valueLength state n)
  False (evaluateHOLFiniteState s (.while mptInsertCondition mptInsertLoopStep)) := by
 let Rank : ∀{F : Type},PanSemStateFiniteExact 64 F→Nat→Prop:=
  fun {F} state n=>MptInsertPathsRank live extensions branches size frontier key length valuePointer valueLength state n
 have exit : ∀{F : Type}(state : PanSemStateFiniteExact 64 F),Rank state 0→∀w : BitVec 64,
  evalHOLFinite state (h:=fun a=>Classical.propDecidable (state.memaddrs a)) mptInsertCondition=some (.val (.word w))→w=0 := by
  intro F state ranked w guard
  rcases ranked with ⟨_,atGo,_⟩|next
  · rw [evalHOLFinite_eq_toExact] at guard
    simpa [mptInsertCondition,evalHOLExact,atGo,Compiler.Encoders.Asm.wordCmpHOL] using guard.symm
  · obtain ⟨node,slot,level,root,a,b,c,d,e,f,g,h,inside,rankEq⟩:=next.active.path
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
  have current : MptInsertPathsActive state live extensions branches size frontier key length valuePointer valueLength (n+1) := by
   rcases ranked with ⟨impossible,_⟩|current
   · omega
   · exact current
  have bounded:=mpt_insert_step_bounded (decClockHOLFinite state) (current.decClock.active.inputs short) installed (by change 2^64+203≤state.clock-1;omega)
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
       · obtain ⟨root,larger,newExtensions,newBranches,newSize,finish,assigned,valid,sub,extSub,branchSub,
          worldOut,kindsOut,pathsOut,transport⟩:=
          mpt_insert_paths_active_stopped (decClockHOLFinite state) post live extensions branches size frontier key length
           valuePointer valueLength (n+1) current.decClock capacity short installed (by change 146≤state.clock-1;omega) stopped run
         have terminal : MptInsertTerminalPaths post live extensions branches key length :=
          ⟨root,larger,newExtensions,newBranches,newSize,finish,assigned,valid,sub,extSub,branchSub,
           worldOut,kindsOut,pathsOut,transport key length current.decClock.keyPath⟩
         exact ⟨0,Nat.zero_le _,Or.inl ⟨rfl,stopped,terminal⟩,metadata.1⟩
       · obtain ⟨nextRank,smaller,nextActive⟩:=mpt_insert_paths_active_step (decClockHOLFinite state) post live extensions branches size frontier key length valuePointer valueLength (n+1)
          current.decClock capacity recordsBefore aligned keyExtent short installed (by change 21≤state.clock-1;omega) stopped run
         exact ⟨nextRank,by omega,Or.inr nextActive,metadata.1⟩
    · exact False.elim (mpt_insert_step_no_continue (decClockHOLFinite state) continued)
  · intro broken
    exact False.elim (mpt_insert_step_no_break (decClockHOLFinite state) broken)
 exact rankedWhile_run mptInsertCondition mptInsertLoopStep (2^64+203) Rank False exit step rank s code (Or.inr active) budget

#print axioms mpt_insert_ranked_loop_paths
end InitECandidate.Runtime
