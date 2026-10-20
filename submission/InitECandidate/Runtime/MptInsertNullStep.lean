import InitECandidate.Runtime.MptInsertFinish
import InitECandidate.Runtime.NodeNewLeafUniformBound
import InitECandidate.Runtime.OriginalNodeNewLeafCode
import InitECandidate.Runtime.NoTopContinue
import InitECandidate.Runtime.RunBounded
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

def mptInsertNewLeafCall : ProgHOL 64 :=
 .call (some (some (.local,ofString "r"),none)) (ofString "node_new_leaf")
  [.op .add [.var .local (ofString "key"),.var .local (ofString "level")],
   .op .sub [.var .local (ofString "klen"),.var .local (ofString "level")],
   .var .local (ofString "vptr"),.var .local (ofString "vlen")]

def mptInsertNonNullStep : ProgHOL 64 :=
 match mptInsertLoopStep with
 | .dec _ _ _ (.dec _ _ _ (.dec _ _ _ (.dec _ _ _ (.seq _ (.seq (.ite _ _ no) _))))) => no
 | _ => .skip

def mptInsertNullStep : ProgHOL 64 :=
 .dec (ofString "r") .one (.const 0)
  (.dec (ofString "next_node") .one (.const 0)
   (.dec (ofString "next_slot") .one (.const 0)
    (.dec (ofString "next_level") .one (.const 0)
     (.seq (.assign .local (ofString "go") (.const 0))
      (.seq mptInsertNewLeafCall mptInsertFinish)))))

theorem source_mptInsert_step : mptInsertLoopStep =
 .dec (ofString "r") .one (.const 0)
  (.dec (ofString "next_node") .one (.const 0)
   (.dec (ofString "next_slot") .one (.const 0)
    (.dec (ofString "next_level") .one (.const 0)
     (.seq (.assign .local (ofString "go") (.const 0))
      (.seq (.ite (.cmp .equal (.var .local (ofString "node")) (.const 0))
       mptInsertNewLeafCall mptInsertNonNullStep) mptInsertFinish))))) := by
 simp only [mptInsertLoopStep,mptInsertNewLeafCall,mptInsertNonNullStep,mptInsertFinish,
  sourceFunctionBody,InitECandidate.Proofs.FrontendCodecComputation.declToHOL_eq]
 rfl

private theorem dec_const_evaluate_congr {F : Type} (s : PanSemStateFiniteExact 64 F)
 (name : MlS) (k : BitVec 64) (a b : ProgHOL 64)
 (same : evaluateHOLFiniteState (setVarHOLFinite name (.val (.word k)) s) a=
  evaluateHOLFiniteState (setVarHOLFinite name (.val (.word k)) s) b) :
 evaluateHOLFiniteState s (.dec name .one (.const k) a)=
  evaluateHOLFiniteState s (.dec name .one (.const k) b) := by
 rw [evaluateHOLFiniteState_dec_total,evaluateHOLFiniteState_dec_total]
 simp only [evalHOLExact,shapeOfHOLExact,shapeEqHOL,if_true]
 rw [same]

private theorem seq_evaluate_congr {F : Type} (s : PanSemStateFiniteExact 64 F)
 (first a b : ProgHOL 64)
 (same : ∀post,evaluateHOLFiniteState s first=(none,post)→
  evaluateHOLFiniteState post a=evaluateHOLFiniteState post b) :
 evaluateHOLFiniteState s (.seq first a)=evaluateHOLFiniteState s (.seq first b) := by
 rw [evaluateHOLFiniteState_seq_line780,evaluateHOLFiniteState_seq_line780]
 cases run : evaluateHOLFiniteState s first with
 | mk result post =>
  cases result with
  | none => exact same post run
  | some result => rfl

/-- With a null current node, the actual loop iteration selects only the
real leaf constructor. This equality includes every error outcome. -/
theorem evaluate_mptInsert_null_step {F : Type} (s : PanSemStateFiniteExact 64 F)
 (node : s.locals.lookup (ofString "node")=some (.val (.word (0#64)))) :
 evaluateHOLFiniteState s mptInsertLoopStep=evaluateHOLFiniteState s mptInsertNullStep := by
 rw [source_mptInsert_step]
 unfold mptInsertNullStep
 apply dec_const_evaluate_congr
 apply dec_const_evaluate_congr
 apply dec_const_evaluate_congr
 apply dec_const_evaluate_congr
 apply seq_evaluate_congr
 intro post reset
 let before :=
  (setVarHOLFinite (ofString "next_level") (.val (.word (0#64)))
   (setVarHOLFinite (ofString "next_slot") (.val (.word (0#64)))
    (setVarHOLFinite (ofString "next_node") (.val (.word (0#64)))
     (setVarHOLFinite (ofString "r") (.val (.word (0#64))) s))))
 change evaluateHOLFiniteState before (.assign .local (ofString "go") (.const (0#64)))=(none,post) at reset
 have kept := evaluate_avoidsLocal_flowing (ofString "node")
  (.assign .local (ofString "go") (.const (0#64))) (by decide) before
 rw [reset] at kept
 have atNode : post.locals.lookup (ofString "node")=some (.val (.word (0#64))) := by
  have same:=kept (Or.inl rfl)
  simpa (config:={decide:=true}) [before,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,node] using same
 rw [evaluateHOLFiniteState_seq_line780,evaluateHOLFiniteState_seq_line780]
 have selected : evaluateHOLFiniteState post (.ite (.cmp .equal (.var .local (ofString "node")) (.const 0)) mptInsertNewLeafCall mptInsertNonNullStep)=evaluateHOLFiniteState post mptInsertNewLeafCall := by
   rw [evaluateHOLFiniteState_ite]
   have guard : @evalHOLExact 64 F _ post.toExact (fun a=>Classical.propDecidable (post.memaddrs a))
    (.cmp .equal (.var .local (ofString "node")) (.const 0))=some (.val (.word (1#64))) := by
    simp [evalHOLExact,atNode,Compiler.Encoders.Asm.wordCmpHOL]
   rw [guard]
   simp
 rw [selected]

/-- The null-node iteration costs at most three clocks, including allocation
failure, invalid arguments and failed stores. No memory or room is assumed. -/
theorem mpt_insert_null_step_bounded {F : Type} (s : PanSemStateFiniteExact 64 F)
 (node : s.locals.lookup (ofString "node")=some (.val (.word (0#64))))
 (code : s.code=originalRuntimeCode) (budget : 3≤s.clock) :
 RunBounded s mptInsertLoopStep 3 := by
 have leaf : FunBounded (ofString "node_new_leaf") 2 :=
  ⟨_,_,_,originalRuntimeCode_nodeNewLeaf_lookup,node_new_leaf_uniform_bounded⟩
 have finish : ProgBounded mptInsertFinish 0 :=
  ProgBounded.straight _ (by rw [source_mptInsert_finish,source_mptInsert_commit,source_mptInsert_advance];rfl)
 have selected : ProgBounded mptInsertNullStep 3 := by
  unfold mptInsertNullStep
  apply ProgBounded.dec
  apply ProgBounded.dec
  apply ProgBounded.dec
  apply ProgBounded.dec
  exact ProgBounded.seq (ProgBounded.straight _ rfl)
   (ProgBounded.seq (ProgBounded.call leaf _ _) finish)
 unfold RunBounded
 rw [evaluate_mptInsert_null_step s node]
 exact selected s code budget

#print axioms evaluate_mptInsert_null_step
#print axioms mpt_insert_null_step_bounded
end InitECandidate.Runtime
