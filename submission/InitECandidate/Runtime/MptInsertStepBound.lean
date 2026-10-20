import InitECandidate.Runtime.MptInsertKindDispatchBound
import InitECandidate.Runtime.MptInsertNullStep
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

def mptInsertInputNames : List MlS :=
 [ofString "node",ofString "key",ofString "klen",ofString "level",ofString "vptr",ofString "vlen"]

structure MptInsertInputs {F : Type} (s : PanSemStateFiniteExact 64 F) : Prop where
 words : ∃node key length level valuePointer valueLength : BitVec 64,
  s.locals.lookup (ofString "node")=some (.val (.word node)) ∧
  s.locals.lookup (ofString "key")=some (.val (.word key)) ∧
  s.locals.lookup (ofString "klen")=some (.val (.word length)) ∧
  s.locals.lookup (ofString "level")=some (.val (.word level)) ∧
  s.locals.lookup (ofString "vptr")=some (.val (.word valuePointer)) ∧
  s.locals.lookup (ofString "vlen")=some (.val (.word valueLength)) ∧
  level.toNat≤length.toNat ∧length.toNat≤18

theorem MptInsertInputs.after_local_frame {F : Type} {s post : PanSemStateFiniteExact 64 F}
 (inputs : MptInsertInputs s)
 (frame : ∀name∈mptInsertInputNames,post.locals.lookup name=s.locals.lookup name) : MptInsertInputs post := by
 obtain ⟨node,key,length,level,valuePointer,valueLength,a,b,c,d,e,f,g,h⟩:=inputs.words
 exact ⟨node,key,length,level,valuePointer,valueLength,
  (frame _ (by simp [mptInsertInputNames])).trans a,(frame _ (by simp [mptInsertInputNames])).trans b,
  (frame _ (by simp [mptInsertInputNames])).trans c,(frame _ (by simp [mptInsertInputNames])).trans d,
  (frame _ (by simp [mptInsertInputNames])).trans e,(frame _ (by simp [mptInsertInputNames])).trans f,g,h⟩

theorem MptInsertInputs.set_local {F : Type} {s : PanSemStateFiniteExact 64 F}
 (inputs : MptInsertInputs s) (name : MlS) (value : ValueHOL 64) (separate : name∉mptInsertInputNames) :
 MptInsertInputs (setVarHOLFinite name value s) := by
 apply inputs.after_local_frame
 intro key member
 have different : key≠name := fun same=>separate (same ▸ member)
 simp [setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,different,Ne.symm different]

theorem mpt_insert_nonnull_step_bounded {F : Type} (s : PanSemStateFiniteExact 64 F)
 (inputs : MptInsertInputs s) (code : s.code=originalRuntimeCode) (budget : 2^64+203≤s.clock) :
 RunBounded s mptInsertNonNullStep (2^64+203) := by
 have sourceForm : mptInsertNonNullStep=
  .dec (ofString "k") .one (.load .one (mptInsertNodeAddress 0)) mptInsertKindDispatch := by
  simp only [mptInsertNonNullStep,mptInsertKindDispatch,mptInsertLoopStep,sourceFunctionBody,
   Proofs.FrontendCodecComputation.declToHOL_eq]
  rfl
 rw [sourceForm]
 apply RunBounded.dec
 intro value evaluated
 have nextInputs:=inputs.set_local (ofString "k") value (by decide)
 obtain ⟨node,key,length,level,valuePointer,valueLength,a,b,c,d,e,f,g,h⟩:=nextInputs.words
 exact mpt_insert_kind_dispatch_bounded _ node key length level valuePointer valueLength a b c d e f g h code budget

/-- One actual original insertion iteration, from indexed typed inputs. The
bound includes all branches, calls, failures, lexical declarations, the go
reset, backlink commit and next-node/level assignments. Loop termination and
preservation of these input facts are separate obligations. -/
theorem mpt_insert_step_bounded {F : Type} (s : PanSemStateFiniteExact 64 F)
 (inputs : MptInsertInputs s) (code : s.code=originalRuntimeCode) (budget : 2^64+203≤s.clock) :
 RunBounded s mptInsertLoopStep (2^64+203) := by
 have body {F : Type} (s : PanSemStateFiniteExact 64 F) (inputs : MptInsertInputs s)
  (code : s.code=originalRuntimeCode) (budget : 2^64+203≤s.clock) :
  RunBounded s (.seq (.assign .local (ofString "go") (.const 0))
   (.seq (.ite (.cmp .equal (.var .local (ofString "node")) (.const 0))
    mptInsertNewLeafCall mptInsertNonNullStep) mptInsertFinish)) (2^64+203) := by
  have resetBound : RunBounded s (.assign .local (ofString "go") (.const 0)) 0:=
   ProgBounded.straight _ rfl s code (by omega)
  have joined : RunBounded s (.seq (.assign .local (ofString "go") (.const 0))
   (.seq (.ite (.cmp .equal (.var .local (ofString "node")) (.const 0))
    mptInsertNewLeafCall mptInsertNonNullStep) mptInsertFinish)) (0+((2^64+203)+0)) := by
   refine RunBounded.seq resetBound (by omega) ?_
   intro ready resetRun readyCode readyBudget
   have readyInputs : MptInsertInputs ready := by
    apply inputs.after_local_frame
    intro name member
    have avoids : avoidsLocal name (.assign .local (ofString "go") (.const (0#64)))=true := by
     simp only [mptInsertInputNames,List.mem_cons,List.not_mem_nil,or_false] at member
     rcases member with rfl|rfl|rfl|rfl|rfl|rfl <;> decide
    have kept:=evaluate_avoidsLocal_flowing name (.assign .local (ofString "go") (.const (0#64))) avoids s
    change evaluateHOLFiniteState s (.assign .local (ofString "go") (.const (0#64)))=(none,ready) at resetRun
    rw [resetRun] at kept
    exact kept (Or.inl rfl)
   have selected : RunBounded ready
    (.ite (.cmp .equal (.var .local (ofString "node")) (.const 0)) mptInsertNewLeafCall mptInsertNonNullStep) (2^64+203) := by
    apply RunBounded.ite
    · have leaf : ProgBounded mptInsertNewLeafCall 3 := ProgBounded.call node_new_leaf_fun_bounded _ _
      exact RunBounded.weaken (leaf ready (readyCode.trans code) (by omega)) (by omega)
    · exact mpt_insert_nonnull_step_bounded ready readyInputs (readyCode.trans code) (by omega)
   refine RunBounded.seq selected readyBudget ?_
   intro next nextRun nextCode nextBudget
   exact ProgBounded.straight _ (by rw [source_mptInsert_finish,source_mptInsert_commit,source_mptInsert_advance];rfl)
    next (nextCode.trans (readyCode.trans code)) nextBudget
  simpa only [Nat.zero_add,Nat.add_zero] using joined
 rw [source_mptInsert_step]
 apply RunBounded.decConst
 apply RunBounded.decConst
 apply RunBounded.decConst
 apply RunBounded.decConst
 exact body _ ((((inputs.set_local (ofString "r") (.val (.word (0#64))) (by decide)).set_local
  (ofString "next_node") (.val (.word (0#64))) (by decide)).set_local
  (ofString "next_slot") (.val (.word (0#64))) (by decide)).set_local
  (ofString "next_level") (.val (.word (0#64))) (by decide)) code budget

#print axioms MptInsertInputs.after_local_frame
#print axioms mpt_insert_nonnull_step_bounded
#print axioms mpt_insert_step_bounded
end InitECandidate.Runtime
