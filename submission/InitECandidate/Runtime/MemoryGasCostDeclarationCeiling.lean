import InitECandidate.Runtime.MemoryGasCostReturnedSizeCeiling
import InitECandidate.Runtime.VmFn_memory_gas_cost
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

theorem memory_gas_cost_declaration_ceiling {F : Type} (s post : PanSemStateFiniteExact 64 F)
 (name : MlS) (argument : ExpHOL 64) (tail : ProgHOL 64) (input : BitVec 64) (value : ValueHOL 64)
 (args : evalListHOLFinite s (h:=fun a=>Classical.propDecidable (s.memaddrs a)) [argument]=some [.val (.word input)])
 (code : s.code=originalRuntimeCode)
 (run : evaluateHOLFiniteState s (.decCall name .one (ofString "memory_gas_cost") [argument] tail)=(some (.returned value),post)) :
 ∃fee : BitVec 64,∃bodyPost output : PanSemStateFiniteExact 64 F,
 evaluateHOLFiniteState (setVarHOLFinite name (.val (.word fee)) {bodyPost with locals:=s.locals}) tail=(some (.returned value),output) ∧
 post={output with locals:=HolFiniteMapExact.resVarEq output.locals (name,s.locals.lookup name)} ∧
 (fee=18446744073709551615#64 ∨input.toNat<2^37) ∧
 bodyPost.memory=s.memory ∧bodyPost.globals=s.globals ∧bodyPost.code=s.code ∧bodyPost.memaddrs=s.memaddrs ∧bodyPost.be=s.be := by
 have installed : s.code.lookup (ofString "memory_gas_cost")=some ([(ofString "size",.one)],sourceFunctionBody Guest.guestFn_memory_gas_cost,.one) := by
  rw [code];exact vmLookup_memory_gas_cost
 let callee : HolFiniteMapExact MlS (ValueHOL 64):=HolFiniteMapExact.empty.update (ofString "size",.val (.word input))
 have lookup:=pan_single_word_lookup s.code.lookup (ofString "memory_gas_cost") (ofString "size") (sourceFunctionBody Guest.guestFn_memory_gas_cost) input installed
 obtain ⟨returned,bodyPost,output,bodyRun,checked,tailRun,postEq⟩:=
  evaluate_decCall_checked_returned_exact_scope s post name (ofString "memory_gas_cost") .one .one _ _ _ tail callee value args lookup run
 obtain ⟨fee,rfl⟩:=value_word_of_shape_one returned ((shapeEqHOL_eq_true _ _).mp checked.1)
 have atSize : (callEntryStateHOLFinite s callee).locals.lookup (ofString "size")=some (.val (.word input)) := by
  simp [callee,callEntryStateHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]
 have ceiling:=memory_gas_cost_returned_size_ceiling (callEntryStateHOLFinite s callee) bodyPost input (.val (.word fee)) atSize code bodyRun
 have bounded : fee=18446744073709551615#64 ∨input.toNat<2^37 := by
  rcases ceiling with equal|small
  · exact Or.inl (HolWordLab.word.inj (ValueHOL.val.inj equal))
  · exact Or.inr small
 have frame:=memoryFrame_of_good vmLookup_memory_gas_cost (by decide) (by decide) (callEntryStateHOLFinite s callee) code
 have metadata:=evaluateHOLFiniteState_metadata (callEntryStateHOLFinite s callee) (sourceFunctionBody Guest.guestFn_memory_gas_cost)
 rw [bodyRun] at frame metadata
 exact ⟨fee,bodyPost,output,tailRun,postEq,bounded,frame.1,frame.2,metadata.1,metadata.2.1,metadata.2.2.1⟩
#print axioms memory_gas_cost_declaration_ceiling
end InitECandidate.Runtime
