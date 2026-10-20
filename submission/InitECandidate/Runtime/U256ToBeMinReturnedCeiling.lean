import InitECandidate.Runtime.U256ToBeMinRuntimeBound
import InitECandidate.Runtime.U256ByteLengthReturnedCeiling
import InitECandidate.Runtime.PanDecCallReturnedGlobalMemoryClockScope
import InitECandidate.Runtime.HtabFindSlotReturned
import InitECandidate.Runtime.AllocationFramedGlobals
import InitECandidate.Runtime.PanWhileNoReturn
import InitECandidate.Runtime.ForkInitSuffixGlobals
import InitECandidate.Runtime.NoDirectReturn
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000
theorem u256_to_be_min_loop_no_return {F : Type} (s : PanSemStateFiniteExact 64 F) (value : ValueHOL 64) :
 (evaluateHOLFiniteState s u256ToBeMinLoopBody).1≠some (.returned value) := by
 intro returned
 have run : evaluateHOLFiniteState s u256ToBeMinLoopBody=(some (.returned value),(evaluateHOLFiniteState s u256ToBeMinLoopBody).2) := Prod.ext returned rfl
 rw [source_u256_to_be_min_loop] at run
 obtain ⟨position,inner,innerRun,_⟩:=dec_returned run
 obtain ⟨values,body,callee,shape,w,bodyPost,args,lookup,bodyRun,resumed,output,globals,code,domain,clock,tailRun,rest⟩:=decCall_returned innerRun
 obtain ⟨middle,storeRun,incrementRun⟩:=seq_returned_of_nonreturning_first
  (fun v=>by unfold u256ToBeMinByteStore; exact evaluate_storeByte_no_return resumed _ _ v) tailRun
 have noReturn:=evaluate_noDirectReturn (.assign .local (ofString "i") (.op .add [.var .local (ofString "i"),.const 1])) rfl middle value
 rw [incrementRun] at noReturn
 exact noReturn rfl

/-- The complete actual minimal writer returns precisely the actual byte-length
callee result. Its coarse ceiling comes from the callee final shift, not an
assumed mathematical bit-length bound or caller-provided result contract. -/
theorem u256_to_be_min_returned_ceiling {F : Type} (s post : PanSemStateFiniteExact 64 F)
 (value : ValueHOL 64) (code : s.code=originalRuntimeCode)
 (run : evaluateHOLFiniteState s (sourceFunctionBody Guest.guestFn_u256_to_be_min)=(some (.returned value),post)) :
 ∃word : BitVec 64,value=.val (.word word) ∧word.toNat<2^61 := by
 rw [tbBody_eq] at run
 change evaluateHOLFiniteState s (.decCall (ofString "len") .one (ofString "u256_byte_length") [.var .local (ofString "a")]
  (.dec (ofString "i") .one (.const 0)
   (.seq (.while (.cmp .lower (.var .local (ofString "i")) (.var .local (ofString "len"))) u256ToBeMinLoopBody)
    (.return (.var .local (ofString "len"))))))=(some (.returned value),post) at run
 obtain ⟨values,body,callee,shape,w,bodyPost,args,lookup,bodyRun,resumed,output,globals,installed,domain,clock,tailRun,rest⟩:=decCall_returned run
 have same:=lookupCodeHOLFinite_installed_body s.code.lookup (ofString "u256_byte_length") _ _ body _ shape values callee
  (by rw [code];exact vmLookup_u256_byte_length) lookup
 subst same
 obtain ⟨actual,actualPost,ready,inner,actualRun,readyLocals,_,_,_,_,_,_,actualTail,_⟩:=
  evaluate_decCall_returned_global_memory_clock_scope s post (ofString "len") (ofString "u256_byte_length") .one shape
   [.var .local (ofString "a")] values (sourceFunctionBody Guest.guestFn_u256_byte_length) _ callee value args lookup run
 obtain ⟨length,actualValue,ceiling⟩:=u256_byte_length_returned_ceiling _ actualPost actual actualRun
 subst actualValue
 obtain ⟨index,loopPost,loopTail,_⟩:=dec_returned actualTail
 obtain ⟨middle,loopRun,returned⟩:=seq_returned_of_nonreturning_first
  (evaluate_while_no_return _ u256ToBeMinLoopBody (fun state v=>u256_to_be_min_loop_no_return state v) _) loopTail
 have lenKept:=evaluate_avoidsLocal_flowing (ofString "len")
  (.while (.cmp .lower (.var .local (ofString "i")) (.var .local (ofString "len"))) u256ToBeMinLoopBody)
  (by decide_cbv) _ (by rw [loopRun];exact Or.inl rfl)
 rw [loopRun] at lenKept
 have atLength : middle.locals.lookup (ofString "len")=some (.val (.word length)) := by
  rw [lenKept]
  simp (config:={decide:=true}) [setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]
 exact ⟨length,return_local_word middle loopPost (ofString "len") length value atLength returned,ceiling⟩
#print axioms u256_to_be_min_loop_no_return
#print axioms u256_to_be_min_returned_ceiling
end InitECandidate.Runtime
