import InitECandidate.Runtime.MloadReadPhysicalContext
import InitECandidate.Runtime.EvmWordDeclarationGeometry
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
theorem mload_saturated_returned_physical_context {F : Type}
 (s post : PanSemStateFiniteExact 64 F) (frame : BitVec 64)
 (words : EvmMemoryOperandWords) (valid : EvmMemoryOperandAt s frame words)
 (sa sb sc sd : BitVec 64) (value : ValueHOL 64)
 (startAt : s.locals.lookup (ofString "start")=some (fundingU256 sa sb sc sd))
 (inside : words.stackSize.toNat<words.stackCapacity.toNat)
 (fullDomain : ∀address : BitVec 64,address.toNat<33806089496→s.memaddrs address)
 (code : s.code=originalRuntimeCode)
 (run : evaluateHOLFiniteState s (mloadAt 2)=(some (.returned value),post)) :
 value=.val (.word 0) ∧EvmMemoryOperandAt post frame {words with pc:=words.pc+1,stackSize:=words.stackSize+1} ∧
 post.globals=s.globals ∧post.memaddrs=s.memaddrs ∧post.be=s.be ∧post.code=s.code ∧
 (∀watched : BitVec 64,frame.toNat≤watched.toNat→watched≠frame+0→watched≠frame+16→post.memory watched=s.memory watched) := by
 rw [source_mload_2] at run
 obtain ⟨body,output,tail,scope,memory,globals,installed,domain,endian⟩:=funding_sat_word_declaration_geometry s post (ofString "s") (.var .local (ofString "start")) (mloadAt 3) sa sb sc sd value (by simp [evalListHOLFinite,evalListHOLExact,evalHOLExact,startAt]) code run
 let ready:=setVarHOLFinite (ofString "s") (.val (.word (evmSatWord sa sb sc sd))) {body with locals:=s.locals}
 change evaluateHOLFiniteState ready (mloadAt 3)=_ at tail
 have readyMemory : ready.memory=s.memory:=memory
 have readyGlobals : ready.globals=s.globals:=globals
 have readyDomain : ready.memaddrs=s.memaddrs:=domain
 have readyCode : ready.code=s.code:=installed
 have readyEndian : ready.be=s.be:=endian
 have physical : EvmMemoryOperandAt ready frame words:=valid.after_context readyGlobals readyMemory readyDomain
 obtain ⟨zero,finalPhysical,finalGlobals,finalDomain,finalEndian,finalCode,upperFrame⟩:=mload_read_returned_physical_context ready output frame words physical (evmSatWord sa sb sc sd) value (by simp [ready,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]) inside (by intro address below;rw [readyDomain];exact fullDomain address below) (readyCode.trans code) tail
 refine ⟨zero,finalPhysical.after_context (by rw [scope]) (by rw [scope]) (by rw [scope]),?_,?_,?_,?_,?_⟩
 · rw [scope,finalGlobals,readyGlobals]
 · rw [scope,finalDomain,readyDomain]
 · rw [scope,finalEndian,readyEndian]
 · rw [scope,finalCode,readyCode]
 · intro watched above notPc notCounter
   rw [scope,upperFrame watched above notPc notCounter,readyMemory]
#print axioms mload_saturated_returned_physical_context
end InitECandidate.Runtime
