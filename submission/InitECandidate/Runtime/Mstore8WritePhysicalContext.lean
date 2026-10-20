import InitECandidate.Runtime.EvmMstore8Source
import InitECandidate.Runtime.ByteStorePhysicalContext
import InitECandidate.Runtime.PcAddReturnPhysicalContext
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
/-- Original MSTORE8 byte write and PC/return tail preserve the full next-opcode
physical state; its actual destination span is below the scratch frontier. -/
theorem mstore8_write_returned_physical_context {F : Type}
 (s post : PanSemStateFiniteExact 64 F) (frame : BitVec 64)
 (words : EvmMemoryOperandWords) (valid : EvmMemoryOperandAt s frame words)
 (start a b c d : BitVec 64) (value : ValueHOL 64)
 (startAt : s.locals.lookup (ofString "s")=some (.val (.word start)))
 (valueAt : s.locals.lookup (ofString "value")=some (fundingU256 a b c d))
 (extent : words.memoryBase.toNat+start.toNat+1≤words.scratchPointer.toNat)
 (code : s.code=originalRuntimeCode)
 (run : evaluateHOLFiniteState s (mstore8At 4)=(some (.returned value),post)) :
 value=.val (.word 0) ∧EvmMemoryOperandAt post frame {words with pc:=words.pc+1} ∧
 post.globals=s.globals ∧post.memaddrs=s.memaddrs ∧post.be=s.be ∧post.code=s.code ∧
 (∀watched : BitVec 64,words.scratchPointer.toNat≤watched.toNat→watched≠frame+0→post.memory watched=s.memory watched) := by
 let destination : ExpHOL 64:=.op .add [fundingLoad 24,.var .local (ofString "s")]
 let expression : ExpHOL 64:=.op .and [.rfield 0 (.var .local (ofString "value")),.const 255]
 have load:=eval_fundingLoad s frame (24#64) words.memoryBase valid.ev (valid.headerDomain 24 (by simp)) valid.memoryBase
 have addressEval : @evalHOLExact 64 F _ s.toExact (fun a=>Classical.propDecidable (s.memaddrs a)) destination=some (.val (.word (words.memoryBase+start))) := by simp [destination,evalHOLExact,evalListHOLExact,load,startAt,wordOpHOL,wordOp,valueIsWord,valueWord]
 have valueEval : @evalHOLExact 64 F _ s.toExact (fun a=>Classical.propDecidable (s.memaddrs a)) expression=some (.val (.word (a&&&255#64))) := by
  simp [expression,evalHOLExact,evalListHOLExact,valueAt,fundingU256,wordOpHOL,wordOp,valueIsWord,valueWord]
  change a&&&(255#64&&&18446744073709551615#64)=a&&&255#64
  have mask : 255#64&&&18446744073709551615#64=255#64 := by decide
  rw [mask]
 have noReturn : ∀v,(evaluateHOLFiniteState s (.storeByte destination expression)).1≠some (.returned v) := by
  intro v;rw [evaluateHOLFiniteState_storeByte,addressEval,valueEval]
  simp only [panMemStoreByteWord8HOL]
  split <;>simp
 rw [source_mstore8_4] at run
 obtain ⟨written,normal,tail⟩:=seq_returned_of_nonreturning_first noReturn run
 have natural : (words.memoryBase+start).toNat=words.memoryBase.toNat+start.toNat:=BitVec.toNat_add_of_lt (by have bound:=words.scratchPointer.isLt;omega)
 have below : (words.memoryBase+start).toNat<words.scratchPointer.toNat := by rw [natural];omega
 obtain ⟨physical,globals,locals,domain,endian,installed,upperFrame⟩:=store_byte_normal_physical_context s written frame words valid destination expression (words.memoryBase+start) (a&&&255#64) below addressEval valueEval normal
 change evaluateHOLFiniteState written (.seq (.call (some (none,none)) (ofString "pc_add") [.const 1]) (.return (.const 0)))=_ at tail
 obtain ⟨zero,finalPhysical,finalGlobals,finalDomain,finalEndian,finalCode,pcFrame⟩:=pc_add_one_return_physical_context written post frame words physical value (installed.trans code) tail
 refine ⟨zero,finalPhysical,finalGlobals.trans globals,finalDomain.trans domain,finalEndian.trans endian,finalCode.trans installed,?_⟩
 intro watched above different
 rw [pcFrame watched different]
 exact upperFrame watched above
#print axioms mstore8_write_returned_physical_context
end InitECandidate.Runtime
