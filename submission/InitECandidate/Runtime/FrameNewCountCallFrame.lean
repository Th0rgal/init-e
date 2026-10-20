import InitECandidate.Runtime.VmFn_htab_count
import InitECandidate.Runtime.PanSingleWordLookup
import InitECandidate.Runtime.PanDecCallCheckedReturnedExactScope
import InitECandidate.Runtime.PanLocalCallNormalResult
import InitECandidate.Runtime.TwoWordValueShape
import InitECandidate.Runtime.HtabSetBound
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
set_option maxRecDepth 100000
set_option maxHeartbeats 3000000
private theorem countFrame : MemoryFrame (sourceFunctionBody Guest.guestFn_htab_count) := by
 apply memoryFrame_leaf
 rw [sourceFunctionBody_eq_structural]
 rfl

/-- The actual original count declaration returns a checked scalar and frames
all memory/workspace, even when its table is otherwise unconstrained. -/
theorem frame_new_count_declaration_returned {F : Type} (s post : PanSemStateFiniteExact 64 F)
 (name : MlS) (argument : ExpHOL 64) (tail : ProgHOL 64) (table : BitVec 64) (value : ValueHOL 64)
 (args : evalListHOLFinite s (h:=fun a=>Classical.propDecidable (s.memaddrs a)) [argument]=some [.val (.word table)])
 (code : s.code=originalRuntimeCode)
 (run : evaluateHOLFiniteState s (.decCall name .one (ofString "htab_count") [argument] tail)=(some (.returned value),post)) :
 ∃count : BitVec 64,∃bodyPost output : PanSemStateFiniteExact 64 F,
 evaluateHOLFiniteState (setVarHOLFinite name (.val (.word count)) {bodyPost with locals:=s.locals}) tail=(some (.returned value),output) ∧
 post={output with locals:=HolFiniteMapExact.resVarEq output.locals (name,s.locals.lookup name)} ∧
 bodyPost.memory=s.memory ∧bodyPost.globals=s.globals ∧bodyPost.memaddrs=s.memaddrs ∧bodyPost.be=s.be ∧bodyPost.code=s.code := by
 have installed : s.code.lookup (ofString "htab_count")=some ([(ofString "t",.one)],sourceFunctionBody Guest.guestFn_htab_count,.one) := by
  rw [code];exact vmLookup_htab_count
 let callee : HolFiniteMapExact MlS (ValueHOL 64):=HolFiniteMapExact.empty.update (ofString "t",.val (.word table))
 have lookup:=pan_single_word_lookup s.code.lookup (ofString "htab_count") (ofString "t") (sourceFunctionBody Guest.guestFn_htab_count) table installed
 obtain ⟨allocated,bodyPost,output,bodyRun,checked,tailRun,postEq⟩:=evaluate_decCall_checked_returned_exact_scope s post name (ofString "htab_count") .one .one _ _ _ _ callee value args lookup run
 obtain ⟨count,rfl⟩:=value_word_of_shape_one allocated ((shapeEqHOL_eq_true _ _).mp checked.1)
 have frame:=countFrame (callEntryStateHOLFinite s callee) code
 have metadata:=evaluateHOLFiniteState_metadata (callEntryStateHOLFinite s callee) (sourceFunctionBody Guest.guestFn_htab_count)
 rw [bodyRun] at frame metadata
 exact ⟨count,bodyPost,output,tailRun,postEq,frame.1,frame.2,metadata.2.1,metadata.2.2.1,metadata.1⟩

/-- The second actual count call assigns a checked scalar to its real caller
local while keeping every old memory word and all workspace globals. -/
theorem frame_new_count_assignment_normal {F : Type} (s post : PanSemStateFiniteExact 64 F)
 (name : MlS) (argument : ExpHOL 64) (table : BitVec 64)
 (args : evalListHOLFinite s (h:=fun a=>Classical.propDecidable (s.memaddrs a)) [argument]=some [.val (.word table)])
 (code : s.code=originalRuntimeCode)
 (run : evaluateHOLFiniteState s (.call (some (some (.local,name),none)) (ofString "htab_count") [argument])=(none,post)) :
 ∃count : BitVec 64,post.locals.lookup name=some (.val (.word count)) ∧
 (∀key,key≠name → post.locals.lookup key=s.locals.lookup key) ∧
 post.memory=s.memory ∧post.globals=s.globals ∧post.memaddrs=s.memaddrs ∧post.be=s.be ∧post.code=s.code := by
 have installed : s.code.lookup (ofString "htab_count")=some ([(ofString "t",.one)],sourceFunctionBody Guest.guestFn_htab_count,.one) := by
  rw [code];exact vmLookup_htab_count
 let callee : HolFiniteMapExact MlS (ValueHOL 64):=HolFiniteMapExact.empty.update (ofString "t",.val (.word table))
 have lookup:=pan_single_word_lookup s.code.lookup (ofString "htab_count") (ofString "t") (sourceFunctionBody Guest.guestFn_htab_count) table installed
 obtain ⟨allocated,bodyPost,bodyRun,checked,postEq⟩:=evaluate_localCall_normal_result s post name (ofString "htab_count") .one [argument] _ _ callee args lookup run
 obtain ⟨count,rfl⟩:=value_word_of_shape_one allocated ((shapeEqHOL_eq_true _ _).mp checked)
 have frame:=countFrame (callEntryStateHOLFinite s callee) code
 have metadata:=evaluateHOLFiniteState_metadata (callEntryStateHOLFinite s callee) (sourceFunctionBody Guest.guestFn_htab_count)
 rw [bodyRun] at frame metadata
 refine ⟨count,?_,?_,?_,?_,?_,?_,?_⟩
 · rw [postEq]
   simp [setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]
 · intro key different
   rw [postEq]
   simp [setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,Ne.symm different]
 · rw [postEq];exact frame.1
 · rw [postEq];exact frame.2
 · rw [postEq];exact metadata.2.1
 · rw [postEq];exact metadata.2.2.1
 · rw [postEq];exact metadata.1
#print axioms frame_new_count_declaration_returned
#print axioms frame_new_count_assignment_normal
end InitECandidate.Runtime
