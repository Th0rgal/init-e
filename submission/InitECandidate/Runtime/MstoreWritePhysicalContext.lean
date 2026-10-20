import InitECandidate.Runtime.EvmMstoreSource
import InitECandidate.Runtime.U256StorePhysicalContext
import InitECandidate.Runtime.PcAddReturnPhysicalContext
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
/-- Actual MSTORE U256 writer, PC and return close the full physical context. -/
theorem mstore_write_returned_physical_context {F : Type}
 (s post : PanSemStateFiniteExact 64 F) (frame : BitVec 64)
 (words : EvmMemoryOperandWords) (valid : EvmMemoryOperandAt s frame words)
 (start a b c d : BitVec 64) (value : ValueHOL 64)
 (startAt : s.locals.lookup (ofString "s")=some (.val (.word start)))
 (valueAt : s.locals.lookup (ofString "value")=some (fundingU256 a b c d))
 (extent : words.memoryBase.toNat+start.toNat+32≤words.scratchPointer.toNat)
 (code : s.code=originalRuntimeCode) (domain : DomOK s.memaddrs)
 (run : evaluateHOLFiniteState s (mstoreAt 4)=(some (.returned value),post)) :
 value=.val (.word 0) ∧EvmMemoryOperandAt post frame {words with pc:=words.pc+1} ∧
 post.globals=s.globals ∧post.memaddrs=s.memaddrs ∧post.be=s.be ∧post.code=s.code ∧
 (∀watched : BitVec 64,words.scratchPointer.toNat≤watched.toNat→watched≠frame+0→post.memory watched=s.memory watched) := by
 let arguments : List (ExpHOL 64):=[.var .local (ofString "value"),.op .add [fundingLoad 24,.var .local (ofString "s")]]
 have load:=eval_fundingLoad s frame (24#64) words.memoryBase valid.ev (valid.headerDomain 24 (by simp)) valid.memoryBase
 have args : evalListHOLFinite s (h:=fun x=>Classical.propDecidable (s.memaddrs x)) arguments=some [fundingU256 a b c d,.val (.word (words.memoryBase+start))] := by simp [arguments,evalListHOLFinite,evalListHOLExact,evalHOLExact,load,startAt,valueAt,wordOpHOL,wordOp,valueIsWord,valueWord]
 rw [source_mstore_4] at run
 obtain ⟨written,normal,tail⟩:=seq_returned_of_nonreturning_first (fun v=>discard_call_not_returned s (ofString "u256_to_be32") arguments v) run
 have natural : (words.memoryBase+start).toNat=words.memoryBase.toNat+start.toNat:=BitVec.toNat_add_of_lt (by have bound:=words.scratchPointer.isLt;omega)
 obtain ⟨physical,globals,locals,domains,endian,installed,upperFrame⟩:=u256_store_discard_normal_physical_context s written frame words valid arguments a b c d (words.memoryBase+start) args (by rw [natural];exact extent) code domain normal
 change evaluateHOLFiniteState written (.seq (.call (some (none,none)) (ofString "pc_add") [.const 1]) (.return (.const 0)))=_ at tail
 obtain ⟨zero,finalPhysical,finalGlobals,finalDomain,finalEndian,finalCode,pcFrame⟩:=pc_add_one_return_physical_context written post frame words physical value (installed.trans code) tail
 refine ⟨zero,finalPhysical,finalGlobals.trans globals,finalDomain.trans domains,finalEndian.trans endian,finalCode.trans installed,?_⟩
 intro watched above different
 rw [pcFrame watched different]
 exact upperFrame watched above
#print axioms mstore_write_returned_physical_context
end InitECandidate.Runtime
