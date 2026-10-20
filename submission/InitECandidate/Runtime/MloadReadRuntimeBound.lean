import InitECandidate.Runtime.U256Read32PhysicalRuntimeBound
import InitECandidate.Runtime.MloadPushRuntimeBound
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
theorem mload_read_tail_bounded {F : Type}
 (s : PanSemStateFiniteExact 64 F) (frame : BitVec 64) (words : EvmMemoryOperandWords)
 (valid : EvmMemoryOperandAt s frame words) (start : BitVec 64)
 (startAt : s.locals.lookup (ofString "s")=some (.val (.word start)))
 (inside : words.stackSize.toNat<words.stackCapacity.toNat)
 (code : s.code=originalRuntimeCode) (budget : 35≤s.clock) :
 RunBounded s (mloadAt 3) 35 := by
 let arguments : List (ExpHOL 64):=[.op .add [fundingLoad 24,.var .local (ofString "s")],.const 32]
 have load:=eval_fundingLoad s frame (24#64) words.memoryBase valid.ev (valid.headerDomain 24 (by simp)) valid.memoryBase
 have args : evalListHOLFinite s (h:=fun x=>Classical.propDecidable (s.memaddrs x)) arguments=some [.val (.word (words.memoryBase+start)),.val (.word 32)] := by simp [arguments,evalListHOLFinite,evalListHOLExact,evalHOLExact,load,startAt,wordOpHOL,wordOp,valueIsWord,valueWord]
 rw [source_mload_3]
 apply runBounded_u256_read32_physical_declaration s frame words valid (ofString "v") (words.memoryBase+start) arguments (mloadAt 4) 2 args code budget
 intro a b c d ready atValue physical installed remaining
 exact mload_push_tail_bounded ready frame words physical inside installed remaining
#print axioms mload_read_tail_bounded
end InitECandidate.Runtime
