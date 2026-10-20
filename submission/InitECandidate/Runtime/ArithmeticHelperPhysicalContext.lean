import InitECandidate.Runtime.ArithmeticPushPhysicalContext
import InitECandidate.Runtime.ArithmeticHelperDeclarationFrame
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
/-- Actual arithmetic helper declaration and push/PC suffix close the next
concrete physical state without assuming a helper execution or frame. -/
theorem arithmetic_helper_returned_physical_context {F : Type}
 (kind : ArithmeticOpcodeKind) (s post : PanSemStateFiniteExact 64 F)
 (frame : BitVec 64) (words : EvmMemoryOperandWords)
 (valid : EvmMemoryOperandAt s frame words)
 (a b c d e f g h : BitVec 64) (value : ValueHOL 64)
 (atX : s.locals.lookup (ofString "x")=some (fundingU256 a b c d))
 (atY : s.locals.lookup (ofString "y")=some (fundingU256 e f g h))
 (inside : words.stackSize.toNat<words.stackCapacity.toNat)
 (fullDomain : ∀address : BitVec 64,address.toNat<33806089496→s.memaddrs address)
 (code : s.code=originalRuntimeCode)
 (run : evaluateHOLFiniteState s (arithmeticOpcodeAt kind 3)=(some (.returned value),post)) :
 value=.val (.word 0) ∧EvmMemoryOperandAt post frame {words with pc:=words.pc+1,stackSize:=words.stackSize+1} ∧
 post.globals=s.globals ∧post.memaddrs=s.memaddrs ∧post.be=s.be ∧post.code=s.code ∧
 (∀watched : BitVec 64,frame.toNat≤watched.toNat→watched≠frame+0→watched≠frame+16→post.memory watched=s.memory watched) := by
 rw [source_arithmetic_opcode_3 kind] at run
 obtain ⟨r0,r1,r2,r3,body,output,tail,scope,memory,globals,domain,endian,installed⟩:=arithmetic_helper_declaration_returned_frame kind s post (ofString "r") [.var .local (ofString "x"),.var .local (ofString "y")] (arithmeticOpcodeAt kind 4) a b c d e f g h value (by simp [evalListHOLFinite,evalListHOLExact,evalHOLExact,atX,atY]) code run
 let ready:=setVarHOLFinite (ofString "r") (fundingU256 r0 r1 r2 r3) {body with locals:=s.locals}
 have readyMemory : ready.memory=s.memory:=memory
 have readyGlobals : ready.globals=s.globals:=globals
 have readyDomain : ready.memaddrs=s.memaddrs:=domain
 have readyCode : ready.code=s.code:=installed
 have physical : EvmMemoryOperandAt ready frame words:=valid.after_context readyGlobals readyMemory readyDomain
 obtain ⟨zero,finalPhysical,finalGlobals,finalDomain,finalEndian,finalCode,upperFrame⟩:=arithmetic_push_returned_physical_context kind ready output frame words physical r0 r1 r2 r3 value (by simp [ready,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]) inside (by intro address below;rw [readyDomain];exact fullDomain address below) (readyCode.trans code) tail
 refine ⟨zero,finalPhysical.after_context (by rw [scope]) (by rw [scope]) (by rw [scope]),?_,?_,?_,?_,?_⟩
 · rw [scope,finalGlobals,readyGlobals]
 · rw [scope,finalDomain,readyDomain]
 · rw [scope,finalEndian];exact endian
 · rw [scope,finalCode,readyCode]
 · intro watched above notPc notCounter
   rw [scope,upperFrame watched above notPc notCounter,readyMemory]
#print axioms arithmetic_helper_returned_physical_context
end InitECandidate.Runtime
