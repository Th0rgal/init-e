import InitECandidate.Runtime.MessageCallGasStipendPrefix
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

/-- The complete original gas calculator, for the zero extra/memory arguments
used by actual CALL opcodes. Stipend boundedness follows from the actual
literal branch, and the allocated word addition does not wrap. -/
theorem message_call_gas_actual_returned_ceiling {F : Type} (s post : PanSemStateFiniteExact 64 F)
 (requested remaining : BitVec 64) (value : ValueHOL 64)
 (atRequested : s.locals.lookup (ofString "gas")=some (.val (.word requested)))
 (atRemaining : s.locals.lookup (ofString "gas_left")=some (.val (.word remaining)))
 (atMemory : s.locals.lookup (ofString "memory_cost")=some (.val (.word (0#64))))
 (atExtra : s.locals.lookup (ofString "extra_gas")=some (.val (.word (0#64))))
 (code : s.code=originalRuntimeCode) (funded : remaining.toNat≤200000000)
 (run : evaluateHOLFiniteState s (sourceFunctionBody Guest.guestFn_calculate_message_call_gas)=(some (.returned value),post)) :
 ∃forwarded allocated stipend : BitVec 64,value=.rStruct [.val (.word forwarded),.val (.word allocated)] ∧
 forwarded≤remaining ∧stipend.toNat≤2300 ∧allocated.toNat=forwarded.toNat+stipend.toNat := by
 have source0 : sourceFunctionBody Guest.guestFn_calculate_message_call_gas=.decCall (ofString "vz") .one (ofString "u256_is_zero") [.var .local (ofString "value")] (messageCallGasAt 1) := by rw [sourceFunctionBody_eq_structural];rfl
 rw [source0] at run
 obtain ⟨zeroFlag,bodyPost,firstOutput,firstRun,firstScope,bodyCode⟩:=funding_word_declaration_returned_context s post (ofString "vz") (ofString "u256_is_zero") _ (messageCallGasAt 1) value run
 let first:=setVarHOLFinite (ofString "vz") (.val (.word zeroFlag)) {bodyPost with locals:=s.locals}
 have atFlag : first.locals.lookup (ofString "vz")=some (.val (.word zeroFlag)) := by simp [first,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]
 obtain ⟨stipend,ready,output,readyRun,_,_,readyCode,atStipend,stipendBound,locals⟩:=message_call_gas_stipend_prefix_returned first firstOutput zeroFlag value atFlag firstRun
 have readyRequested : ready.locals.lookup (ofString "gas")=some (.val (.word requested)) := by
  rw [locals _ (by decide)]
  simpa (config:={decide:=true}) [first,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE] using atRequested
 have readyRemaining : ready.locals.lookup (ofString "gas_left")=some (.val (.word remaining)) := by
  rw [locals _ (by decide)]
  simpa (config:={decide:=true}) [first,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE] using atRemaining
 have readyMemory : ready.locals.lookup (ofString "memory_cost")=some (.val (.word (0#64))) := by
  rw [locals _ (by decide)]
  simpa (config:={decide:=true}) [first,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE] using atMemory
 have readyExtra : ready.locals.lookup (ofString "extra_gas")=some (.val (.word (0#64))) := by
  rw [locals _ (by decide)]
  simpa (config:={decide:=true}) [first,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE] using atExtra
 have readyOriginal : ready.code=originalRuntimeCode:=readyCode.trans (bodyCode.trans code)
 obtain ⟨finalOutput,finalRun,_⟩:=message_call_gas_zero_need_returned_context ready output remaining value readyRemaining readyMemory readyExtra readyOriginal readyRun
 let arithmetic:=setVarHOLFinite (ofString "need") (.val (.word (0#64))) {ready with clock:=ready.clock-1}
 have arithmeticRequested : arithmetic.locals.lookup (ofString "gas")=some (.val (.word requested)) := by simpa (config:={decide:=true}) [arithmetic,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE] using readyRequested
 have arithmeticRemaining : arithmetic.locals.lookup (ofString "gas_left")=some (.val (.word remaining)) := by simpa (config:={decide:=true}) [arithmetic,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE] using readyRemaining
 have arithmeticMemory : arithmetic.locals.lookup (ofString "memory_cost")=some (.val (.word (0#64))) := by simpa (config:={decide:=true}) [arithmetic,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE] using readyMemory
 have arithmeticExtra : arithmetic.locals.lookup (ofString "extra_gas")=some (.val (.word (0#64))) := by simpa (config:={decide:=true}) [arithmetic,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE] using readyExtra
 have arithmeticStipend : arithmetic.locals.lookup (ofString "stipend")=some (.val (.word stipend)) := by simpa (config:={decide:=true}) [arithmetic,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE] using atStipend
 obtain ⟨forwarded,allocated,returned,below,exactAllocation,_⟩:=message_call_gas_arithmetic_tail_ceiling arithmetic finalOutput requested remaining stipend value arithmeticRequested arithmeticRemaining arithmeticMemory arithmeticExtra arithmeticStipend funded stipendBound finalRun
 exact ⟨forwarded,allocated,stipend,returned,below,stipendBound,exactAllocation⟩
#print axioms message_call_gas_actual_returned_ceiling
end InitECandidate.Runtime
