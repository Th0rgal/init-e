import InitECandidate.Runtime.StackPushNoGrowthCallPhysicalContext
import InitECandidate.Runtime.EvmMloadSource
import InitECandidate.Runtime.PcAddReturnPhysicalContext
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
/-- Real MLOAD push and PC/return suffix close the next physical opcode state. -/
theorem mload_push_returned_physical_context {F : Type}
 (s post : PanSemStateFiniteExact 64 F) (frame : BitVec 64)
 (words : EvmMemoryOperandWords) (valid : EvmMemoryOperandAt s frame words)
 (a b c d : BitVec 64) (value : ValueHOL 64)
 (atValue : s.locals.lookup (ofString "v")=some (fundingU256 a b c d))
 (inside : words.stackSize.toNat<words.stackCapacity.toNat)
 (fullDomain : ∀address : BitVec 64,address.toNat<33806089496→s.memaddrs address)
 (code : s.code=originalRuntimeCode)
 (run : evaluateHOLFiniteState s (mloadAt 4)=(some (.returned value),post)) :
 value=.val (.word 0) ∧EvmMemoryOperandAt post frame {words with pc:=words.pc+1,stackSize:=words.stackSize+1} ∧
 post.globals=s.globals ∧post.memaddrs=s.memaddrs ∧post.be=s.be ∧post.code=s.code ∧
 (∀watched : BitVec 64,frame.toNat≤watched.toNat→watched≠frame+0→watched≠frame+16→post.memory watched=s.memory watched) := by
 rw [source_mload_4] at run
 obtain ⟨next,pushed,tail⟩:=seq_returned_of_nonreturning_first (fun v=>discard_call_not_returned s (ofString "stack_push") [.var .local (ofString "v")] v) run
 obtain ⟨physical,globals,locals,domain,endian,installed,pushFrame⟩:=stack_push_no_growth_discard_physical_context s next frame words valid [.var .local (ofString "v")] a b c d (by simp [evalListHOLFinite,evalListHOLExact,evalHOLExact,atValue]) inside fullDomain code pushed
 change evaluateHOLFiniteState next (.seq (.call (some (none,none)) (ofString "pc_add") [.const 1]) (.return (.const 0)))=_ at tail
 obtain ⟨zero,finalPhysical,finalGlobals,finalDomain,finalEndian,finalCode,pcFrame⟩:=pc_add_one_return_physical_context next post frame {words with stackSize:=words.stackSize+1} physical value (installed.trans code) tail
 refine ⟨zero,finalPhysical,finalGlobals.trans globals,finalDomain.trans domain,finalEndian.trans endian,finalCode.trans installed,?_⟩
 intro watched above notPc notCounter
 rw [pcFrame watched notPc]
 exact pushFrame watched above notCounter
#print axioms mload_push_returned_physical_context
end InitECandidate.Runtime
