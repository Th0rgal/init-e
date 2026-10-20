import InitECandidate.Runtime.Mstore8WritePhysicalContext
import InitECandidate.Runtime.EvmWordDeclarationGeometry
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
/-- Actual saturation and full byte-store/PC tail retain the next physical
context. The whole opcode will derive this span from its own charge. -/
theorem mstore8_saturated_returned_physical_context {F : Type}
 (s post : PanSemStateFiniteExact 64 F) (frame : BitVec 64)
 (words : EvmMemoryOperandWords) (valid : EvmMemoryOperandAt s frame words)
 (sa sb sc sd a b c d : BitVec 64) (value : ValueHOL 64)
 (startAt : s.locals.lookup (ofString "start")=some (fundingU256 sa sb sc sd))
 (valueAt : s.locals.lookup (ofString "value")=some (fundingU256 a b c d))
 (extent : words.memoryBase.toNat+(evmSatWord sa sb sc sd).toNat+1≤words.scratchPointer.toNat)
 (code : s.code=originalRuntimeCode)
 (run : evaluateHOLFiniteState s (mstore8At 3)=(some (.returned value),post)) :
 value=.val (.word 0) ∧EvmMemoryOperandAt post frame {words with pc:=words.pc+1} ∧
 post.globals=s.globals ∧post.memaddrs=s.memaddrs ∧post.be=s.be ∧post.code=s.code ∧
 (∀watched : BitVec 64,words.scratchPointer.toNat≤watched.toNat→watched≠frame+0→post.memory watched=s.memory watched) := by
 rw [source_mstore8_3] at run
 obtain ⟨body,output,tail,scope,memory,globals,installed,domain,endian⟩:=funding_sat_word_declaration_geometry s post (ofString "s") (.var .local (ofString "start")) (mstore8At 4) sa sb sc sd value (by simp [evalListHOLFinite,evalListHOLExact,evalHOLExact,startAt]) code run
 let ready:=setVarHOLFinite (ofString "s") (.val (.word (evmSatWord sa sb sc sd))) {body with locals:=s.locals}
 change evaluateHOLFiniteState ready (mstore8At 4)=_ at tail
 have readyMemory : ready.memory=s.memory:=memory
 have readyGlobals : ready.globals=s.globals:=globals
 have readyDomain : ready.memaddrs=s.memaddrs:=domain
 have readyCode : ready.code=s.code:=installed
 have readyEndian : ready.be=s.be:=endian
 have physical : EvmMemoryOperandAt ready frame words:=valid.after_context readyGlobals readyMemory readyDomain
 obtain ⟨zero,finalPhysical,finalGlobals,finalDomain,finalEndian,finalCode,upperFrame⟩:=mstore8_write_returned_physical_context ready output frame words physical (evmSatWord sa sb sc sd) a b c d value (by simp [ready,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]) (by simpa (config:={decide:=true}) [ready,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE] using valueAt) extent (readyCode.trans code) tail
 refine ⟨zero,finalPhysical.after_context (by rw [scope]) (by rw [scope]) (by rw [scope]),?_,?_,?_,?_,?_⟩
 · rw [scope,finalGlobals,readyGlobals]
 · rw [scope,finalDomain,readyDomain]
 · rw [scope,finalEndian,readyEndian]
 · rw [scope,finalCode,readyCode]
 · intro watched above different
   rw [scope,upperFrame watched above different,readyMemory]
#print axioms mstore8_saturated_returned_physical_context
end InitECandidate.Runtime
