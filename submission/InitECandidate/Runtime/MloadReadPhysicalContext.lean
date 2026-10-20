import InitECandidate.Runtime.MloadPushPhysicalContext
import InitECandidate.Runtime.U256FromBeDeclarationFrame
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
/-- Actual read gives the checked real four-word push operand, with all old
physical memory/global cells kept by the real converter. -/
theorem mload_read_returned_physical_context {F : Type}
 (s post : PanSemStateFiniteExact 64 F) (frame : BitVec 64)
 (words : EvmMemoryOperandWords) (valid : EvmMemoryOperandAt s frame words)
 (start : BitVec 64) (value : ValueHOL 64)
 (startAt : s.locals.lookup (ofString "s")=some (.val (.word start)))
 (inside : words.stackSize.toNat<words.stackCapacity.toNat)
 (fullDomain : ∀address : BitVec 64,address.toNat<33806089496→s.memaddrs address)
 (code : s.code=originalRuntimeCode)
 (run : evaluateHOLFiniteState s (mloadAt 3)=(some (.returned value),post)) :
 value=.val (.word 0) ∧EvmMemoryOperandAt post frame {words with pc:=words.pc+1,stackSize:=words.stackSize+1} ∧
 post.globals=s.globals ∧post.memaddrs=s.memaddrs ∧post.be=s.be ∧post.code=s.code ∧
 (∀watched : BitVec 64,frame.toNat≤watched.toNat→watched≠frame+0→watched≠frame+16→post.memory watched=s.memory watched) := by
 let arguments : List (ExpHOL 64):=[.op .add [fundingLoad 24,.var .local (ofString "s")],.const 32]
 have load:=eval_fundingLoad s frame (24#64) words.memoryBase valid.ev (valid.headerDomain 24 (by simp)) valid.memoryBase
 have args : evalListHOLFinite s (h:=fun x=>Classical.propDecidable (s.memaddrs x)) arguments=some [.val (.word (words.memoryBase+start)),.val (.word 32)] := by simp [arguments,evalListHOLFinite,evalListHOLExact,evalHOLExact,load,startAt,wordOpHOL,wordOp,valueIsWord,valueWord]
 rw [source_mload_3] at run
 obtain ⟨a,b,c,d,body,output,tail,scope,memory,globals,domain,endian,installed⟩:=u256_from_be_declaration_returned_frame s post (ofString "v") arguments (mloadAt 4) (words.memoryBase+start) 32 value args code run
 let ready:=setVarHOLFinite (ofString "v") (fundingU256 a b c d) {body with locals:=s.locals}
 change evaluateHOLFiniteState ready (mloadAt 4)=_ at tail
 have readyMemory : ready.memory=s.memory:=memory
 have readyGlobals : ready.globals=s.globals:=globals
 have readyDomain : ready.memaddrs=s.memaddrs:=domain
 have readyCode : ready.code=s.code:=installed
 have readyEndian : ready.be=s.be:=endian
 have physical : EvmMemoryOperandAt ready frame words:=valid.after_context readyGlobals readyMemory readyDomain
 obtain ⟨zero,finalPhysical,finalGlobals,finalDomain,finalEndian,finalCode,upperFrame⟩:=mload_push_returned_physical_context ready output frame words physical a b c d value (by simp [ready,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]) inside (by intro address below;rw [readyDomain];exact fullDomain address below) (readyCode.trans code) tail
 refine ⟨zero,finalPhysical.after_context (by rw [scope]) (by rw [scope]) (by rw [scope]),?_,?_,?_,?_,?_⟩
 · rw [scope,finalGlobals,readyGlobals]
 · rw [scope,finalDomain,readyDomain]
 · rw [scope,finalEndian,readyEndian]
 · rw [scope,finalCode,readyCode]
 · intro watched above notPc notCounter
   rw [scope,upperFrame watched above notPc notCounter,readyMemory]
#print axioms mload_read_returned_physical_context
end InitECandidate.Runtime
