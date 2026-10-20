import InitECandidate.Runtime.MptInsertRankedLoop
import InitECandidate.Runtime.PanDecReturnedScope
import InitECandidate.Runtime.PanWhileNoReturn
import InitECandidate.Runtime.NoDirectReturn
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

def mptInsertBodyReady {F : Type} (s : PanSemStateFiniteExact 64 F) : PanSemStateFiniteExact 64 F :=
 setVarHOLFinite (ofString "go") (.val (.word (1#64)))
  (setVarHOLFinite (ofString "slot") (.val (.word (0#64)))
   (setVarHOLFinite (ofString "result") (.val (.word (0#64))) s))

private theorem const_dec_returned_scope {F : Type} (s post : PanSemStateFiniteExact 64 F)
 (name : MlS) (k : BitVec 64) (body : ProgHOL 64) (returned : ValueHOL 64)
 (run : evaluateHOLFiniteState s (.dec name .one (.const k) body)=(some (.returned returned),post)) :
 ∃output,evaluateHOLFiniteState (setVarHOLFinite name (.val (.word k)) s) body=(some (.returned returned),output) ∧
 post={output with locals:=HolFiniteMapExact.resVarEq output.locals (name,s.locals.lookup name)} := by
 obtain ⟨value,output,evaluated,bodyRun,scope⟩:=evaluate_dec_returned_scope s post name .one (.const k) body returned run
 have same : value=.val (.word k):=Option.some.inj evaluated.symm
 subst value
 exact ⟨output,bodyRun,scope⟩

/-- A returned original insertion body must reach its real final return:
callee returns are consumed inside the loop and cannot escape it. -/
theorem mpt_insert_body_returned_scope {F : Type} (s post : PanSemStateFiniteExact 64 F)
 (returned : ValueHOL 64)
 (run : evaluateHOLFiniteState s (sourceFunctionBody Guest.guestFn__mpt_insert_node)=
  (some (.returned returned),post)) :
 ∃loopPost output : PanSemStateFiniteExact 64 F,
 evaluateHOLFiniteState (mptInsertBodyReady s) (.while mptInsertCondition mptInsertLoopStep)=(none,loopPost) ∧
 evaluateHOLFiniteState loopPost (.return (.var .local (ofString "result")))=(some (.returned returned),output) ∧
 post.memory=output.memory ∧post.globals=output.globals ∧post.memaddrs=output.memaddrs ∧post.be=output.be := by
 rw [source_mptInsert_body] at run
 obtain ⟨firstOutput,firstRun,firstScope⟩:=const_dec_returned_scope s post (ofString "result") 0 _ returned run
 let first:=setVarHOLFinite (ofString "result") (.val (.word (0#64))) s
 change evaluateHOLFiniteState first _=(some (.returned returned),firstOutput) at firstRun
 obtain ⟨secondOutput,secondRun,secondScope⟩:=const_dec_returned_scope first firstOutput (ofString "slot") 0 _ returned firstRun
 let second:=setVarHOLFinite (ofString "slot") (.val (.word (0#64))) first
 change evaluateHOLFiniteState second _=(some (.returned returned),secondOutput) at secondRun
 obtain ⟨output,coreRun,thirdScope⟩:=const_dec_returned_scope second secondOutput (ofString "go") 1 _ returned secondRun
 change evaluateHOLFiniteState (mptInsertBodyReady s)
  (.seq (.while mptInsertCondition mptInsertLoopStep) (.return (.var .local (ofString "result"))))=
  (some (.returned returned),output) at coreRun
 have noReturn : ∀value,(evaluateHOLFiniteState (mptInsertBodyReady s)
  (.while mptInsertCondition mptInsertLoopStep)).1≠some (.returned value) := by
  intro value
  apply evaluate_while_no_return
  intro state result
  apply evaluate_noDirectReturn
  simp only [mptInsertLoopStep,sourceFunctionBody,Proofs.FrontendCodecComputation.declToHOL_eq]
  decide
 rw [evaluateHOLFiniteState_seq_line780] at coreRun
 cases loopRun : evaluateHOLFiniteState (mptInsertBodyReady s) (.while mptInsertCondition mptInsertLoopStep) with
 | mk result loopPost =>
   rw [loopRun] at coreRun noReturn
   cases result with
   | none =>
     refine ⟨loopPost,output,rfl,coreRun,?_,?_,?_,?_⟩ <;>rw [firstScope,secondScope,thirdScope]
   | some result =>
     cases result with
     | returned value => exact False.elim (noReturn value rfl)
     | _ => cases coreRun

#print axioms mpt_insert_body_returned_scope
end InitECandidate.Runtime
