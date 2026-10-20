import InitECandidate.Runtime.MptInsertSelectedFinishWorld
import InitECandidate.Runtime.PanZeroDecNormalScope
import InitECandidate.Runtime.LocalAssignNormalValue
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- Actual continuing selection cannot be the null-node leaf constructor. -/
theorem mpt_insert_selected_finish_running_nonzero {F : Type}
 (s post : PanSemStateFiniteExact 64 F) (node : BitVec 64)
 (atNode : s.locals.lookup (ofString "node")=some (.val (.word node)))
 (zero : s.locals.lookup (ofString "go")=some (.val (.word (0#64))))
 (running : post.locals.lookup (ofString "go")≠some (.val (.word (0#64))))
 (run : evaluateHOLFiniteState s mptInsertSelectedFinish=(none,post)) : node≠0#64 := by
 unfold mptInsertSelectedFinish at run
 obtain ⟨selected,selectedRun,finishRun⟩:=seq_normal_parts run
 have finishGo : post.locals.lookup (ofString "go")=selected.locals.lookup (ofString "go") := by
  have avoids : avoidsLocal (ofString "go") mptInsertFinish=true := by
   rw [source_mptInsert_finish,source_mptInsert_commit,source_mptInsert_advance];decide
  have kept:=evaluate_avoidsLocal_flowing (ofString "go") mptInsertFinish avoids selected
  rw [finishRun] at kept
  exact kept (Or.inl rfl)
 have selectedRunning : selected.locals.lookup (ofString "go")≠some (.val (.word (0#64))) := by
  intro stopped;apply running;rw [finishGo];exact stopped
 have cmp : @evalHOLExact 64 F _ s.toExact (fun a=>Classical.propDecidable (s.memaddrs a))
  (.cmp .equal (.var .local (ofString "node")) (.const (0#64)))=
  some (.val (.word (if node=0#64 then 1#64 else 0#64))) := by
  simp [evalHOLExact,atNode,Compiler.Encoders.Asm.wordCmpHOL]
 rw [evaluateHOLFiniteState_ite,cmp] at selectedRun
 have nonzero : node≠0#64 := by
  intro null
  have actual:=selectedRun
  simp only [if_pos null,show (1#64)≠0 from by decide,if_false] at actual
  exact selectedRunning (mpt_insert_new_leaf_normal_stopped s selected zero actual)
 exact nonzero

/-- The complete continuing iteration therefore started at a non-null node,
including its local declarations and reset. No memory invariant is needed. -/
theorem mpt_insert_step_running_nonzero {F : Type}
 (s post : PanSemStateFiniteExact 64 F) (node : BitVec 64)
 (atNode : s.locals.lookup (ofString "node")=some (.val (.word node)))
 (running : post.locals.lookup (ofString "go")≠some (.val (.word (0#64))))
 (run : evaluateHOLFiniteState s mptInsertLoopStep=(none,post)) : node≠0#64 := by
 rw [source_mptInsert_step] at run
 obtain ⟨outR,runR,scopeR⟩:=evaluate_zero_dec_normal_scope s post (ofString "r") _ run
 let first:=setVarHOLFinite (ofString "r") (.val (.word (0#64))) s
 change evaluateHOLFiniteState first _=(none,outR) at runR
 obtain ⟨outN,runN,scopeN⟩:=evaluate_zero_dec_normal_scope first outR (ofString "next_node") _ runR
 let second:=setVarHOLFinite (ofString "next_node") (.val (.word (0#64))) first
 change evaluateHOLFiniteState second _=(none,outN) at runN
 obtain ⟨outS,runS,scopeS⟩:=evaluate_zero_dec_normal_scope second outN (ofString "next_slot") _ runN
 let third:=setVarHOLFinite (ofString "next_slot") (.val (.word (0#64))) second
 change evaluateHOLFiniteState third _=(none,outS) at runS
 obtain ⟨output,runL,scopeL⟩:=evaluate_zero_dec_normal_scope third outS (ofString "next_level") _ runS
 let fourth:=setVarHOLFinite (ofString "next_level") (.val (.word (0#64))) third
 change evaluateHOLFiniteState fourth (.seq (.assign .local (ofString "go") (.const (0#64))) mptInsertSelectedFinish)=(none,output) at runL
 obtain ⟨reset,resetRun,coreRun⟩:=seq_normal_parts runL
 obtain ⟨resetValue,resetEval,resetEq⟩:=evaluate_local_assign_normal_value fourth reset (ofString "go") (.const (0#64)) resetRun
 have resetZero : resetValue=.val (.word (0#64)):=Option.some.inj resetEval.symm
 subst resetValue
 subst reset
 let entered:=setVarHOLFinite (ofString "go") (.val (.word (0#64))) fourth
 change evaluateHOLFiniteState entered mptInsertSelectedFinish=(none,output) at coreRun
 have kept (name : MlS) (a : name≠ofString "r") (b : name≠ofString "next_node")
  (c : name≠ofString "next_slot") (d : name≠ofString "next_level") (e : name≠ofString "go") :
  entered.locals.lookup name=s.locals.lookup name := by
  simp [entered,fourth,third,second,first,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,a,b,c,d,e,
   Ne.symm a,Ne.symm b,Ne.symm c,Ne.symm d,Ne.symm e]
 have restored (name : MlS) (a : name≠ofString "r") (b : name≠ofString "next_node")
  (c : name≠ofString "next_slot") (d : name≠ofString "next_level") :
  post.locals.lookup name=output.locals.lookup name := by
  rw [scopeR,saved_local_lookup_other outR.locals (ofString "r") name _ a]
  rw [scopeN,saved_local_lookup_other outN.locals (ofString "next_node") name _ b]
  rw [scopeS,saved_local_lookup_other outS.locals (ofString "next_slot") name _ c]
  rw [scopeL,saved_local_lookup_other output.locals (ofString "next_level") name _ d]
 have outputRunning : output.locals.lookup (ofString "go")≠some (.val (.word (0#64))) := by
  intro stopped;apply running;rw [restored _ (by decide) (by decide) (by decide) (by decide)];exact stopped
 apply mpt_insert_selected_finish_running_nonzero entered output node
 · exact (kept _ (by decide) (by decide) (by decide) (by decide) (by decide)).trans atNode
 · simp (config:={decide:=true}) [entered,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]
 · exact outputRunning
 · exact coreRun

#print axioms mpt_insert_selected_finish_running_nonzero
#print axioms mpt_insert_step_running_nonzero
end InitECandidate.Runtime
