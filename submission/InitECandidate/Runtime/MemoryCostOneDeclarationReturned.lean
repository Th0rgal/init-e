import InitECandidate.Runtime.MemoryCostOneReturnedExpansion
import InitECandidate.Runtime.VmFn_extend_memory_cost1
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
/-- Actual installed cost1 declaration with arbitrary source argument
expressions: successful evaluator checks and the original body derive the
returned two-word expansion and exact continuation. -/
theorem memory_cost_one_declaration_returned {F : Type} (s post : PanSemStateFiniteExact 64 F)
 (name : MlS) (arguments : List (ExpHOL 64)) (tail : ProgHOL 64)
 (frame current : BitVec 64) (value : ValueHOL 64)
 (atFrame : s.globals.lookup (ofString "ev")=some (.val (.word frame)))
 (domain : s.memaddrs (frame+32)) (currentAt : s.memory (frame+32)=.word current)
 (code : s.code=originalRuntimeCode)
 (run : evaluateHOLFiniteState s (.decCall name (.comb [.one,.one]) (ofString "extend_memory_cost1") arguments tail)=(some (.returned value),post)) :
 ∃fee expansion : BitVec 64,∃bodyPost output : PanSemStateFiniteExact 64 F,
 evaluateHOLFiniteState (setVarHOLFinite name (.rStruct [.val (.word fee),.val (.word expansion)]) {bodyPost with locals:=s.locals}) tail=(some (.returned value),output) ∧
 post={output with locals:=HolFiniteMapExact.resVarEq output.locals (name,s.locals.lookup name)} ∧
 current.toNat+expansion.toNat<2^64 ∧bodyPost.memory=s.memory ∧bodyPost.globals=s.globals ∧
 bodyPost.code=s.code ∧bodyPost.memaddrs=s.memaddrs ∧bodyPost.be=s.be := by
 obtain ⟨values,body,callee,returnShape,_,_,args,lookup,_⟩:=decCall_returned run
 obtain ⟨params,rs,installed⟩:=lookupCode_installed lookup
 rw [code,vmLookup_extend_memory_cost1] at installed
 simp only [Option.some.injEq,Prod.mk.injEq] at installed
 obtain ⟨rfl,rfl,rfl⟩:=installed
 obtain ⟨returned,bodyPost,output,bodyRun,checked,tailRun,postEq⟩:=
  evaluate_decCall_checked_returned_exact_scope s post name (ofString "extend_memory_cost1") (.comb [.one,.one]) returnShape arguments values _ tail callee value args lookup run
 obtain ⟨fee,expansion,returnedEq,bounded⟩:=memory_cost_one_returned_expansion (callEntryStateHOLFinite s callee) bodyPost frame current returned atFrame domain currentAt code bodyRun
 subst returned
 have frameKept:=memoryFrame_of_good vmLookup_extend_memory_cost1 (by decide) (by decide) (callEntryStateHOLFinite s callee) code
 have metadata:=evaluateHOLFiniteState_metadata (callEntryStateHOLFinite s callee) (sourceFunctionBody Guest.guestFn_extend_memory_cost1)
 rw [bodyRun] at frameKept metadata
 exact ⟨fee,expansion,bodyPost,output,tailRun,postEq,bounded,frameKept.1,frameKept.2,metadata.1,metadata.2.1,metadata.2.2.1⟩
#print axioms memory_cost_one_declaration_returned
end InitECandidate.Runtime
