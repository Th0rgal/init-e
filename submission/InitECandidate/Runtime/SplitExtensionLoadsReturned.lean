import InitECandidate.Runtime.SplitExtensionSource
import InitECandidate.Runtime.LocalWordFieldEval
import InitECandidate.Runtime.PanDecReturnedScope
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

def splitExtensionLoadedState {F : Type} (s : PanSemStateFiniteExact 64 F)
 (segment length child : BitVec 64) : PanSemStateFiniteExact 64 F :=
 setVarHOLFinite (ofString "child") (.val (.word child))
  (setVarHOLFinite (ofString "sl") (.val (.word length))
   (setVarHOLFinite (ofString "seg") (.val (.word segment)) s))

/-- The three actual field loads reach the original branch-allocation tail;
only lexical locals are restored after that tail returns. -/
theorem split_extension_loads_returned_scope {F : Type}
 (s post : PanSemStateFiniteExact 64 F) (node segment length child : BitVec 64)
 (atNode : s.locals.lookup (ofString "node")=some (.val (.word node)))
 (domain32 : s.memaddrs (node+32#64)) (domain40 : s.memaddrs (node+40#64))
 (domain48 : s.memaddrs (node+48#64))
 (memory32 : s.memory (node+32#64)=.word segment)
 (memory40 : s.memory (node+40#64)=.word length)
 (memory48 : s.memory (node+48#64)=.word child)
 (returned : ValueHOL 64)
 (run : evaluateHOLFiniteState s (splitExtensionAt 0)=(some (.returned returned),post)) :
 ∃output,evaluateHOLFiniteState (splitExtensionLoadedState s segment length child) (splitExtensionAt 3)=
  (some (.returned returned),output) ∧post.memory=output.memory ∧post.globals=output.globals ∧
  post.memaddrs=output.memaddrs ∧post.be=output.be := by
 rw [source_split_extension_0] at run
 obtain ⟨value0,out0,init0,body0,scope0⟩:=evaluate_dec_returned_scope s post (ofString "seg") .one
  (.load .one (.op .add [.var .local (ofString "node"),.const 32])) (splitExtensionAt 1) returned run
 have eval0:=eval_local_word_field s (ofString "node") node 32 segment atNode domain32 memory32
 have eq0 : value0=.val (.word segment):=Option.some.inj (init0.symm.trans eval0)
 subst value0
 let first:=setVarHOLFinite (ofString "seg") (.val (.word segment)) s
 change evaluateHOLFiniteState first (splitExtensionAt 1)=(some (.returned returned),out0) at body0
 rw [source_split_extension_1] at body0
 obtain ⟨value1,out1,init1,body1,scope1⟩:=evaluate_dec_returned_scope first out0 (ofString "sl") .one
  (.load .one (.op .add [.var .local (ofString "node"),.const 40])) (splitExtensionAt 2) returned body0
 have firstNode : first.locals.lookup (ofString "node")=some (.val (.word node)):=by
  simpa (config:={decide:=true}) [first,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE] using atNode
 have eval1:=eval_local_word_field first (ofString "node") node 40 length firstNode domain40 memory40
 have eq1 : value1=.val (.word length):=Option.some.inj (init1.symm.trans eval1)
 subst value1
 let second:=setVarHOLFinite (ofString "sl") (.val (.word length)) first
 change evaluateHOLFiniteState second (splitExtensionAt 2)=(some (.returned returned),out1) at body1
 rw [source_split_extension_2] at body1
 obtain ⟨value2,out2,init2,body2,scope2⟩:=evaluate_dec_returned_scope second out1 (ofString "child") .one
  (.load .one (.op .add [.var .local (ofString "node"),.const 48])) (splitExtensionAt 3) returned body1
 have secondNode : second.locals.lookup (ofString "node")=some (.val (.word node)):=by
  simpa (config:={decide:=true}) [second,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE] using firstNode
 have eval2:=eval_local_word_field second (ofString "node") node 48 child secondNode domain48 memory48
 have eq2 : value2=.val (.word child):=Option.some.inj (init2.symm.trans eval2)
 subst value2
 refine ⟨out2,body2,?_,?_,?_,?_⟩ <;> rw [scope0,scope1,scope2]

#print axioms split_extension_loads_returned_scope
end InitECandidate.Runtime
