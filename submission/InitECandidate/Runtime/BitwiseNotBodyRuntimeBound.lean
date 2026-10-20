import InitECandidate.Runtime.BitwiseNotPushRuntimeBound
import InitECandidate.Runtime.ChargeGasPhysicalContext
import InitECandidate.Runtime.StackPopPhysicalRuntimeBound
import InitECandidate.Runtime.VmFn_charge_gas
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
private theorem not_charge_bounded : ProgBounded (.call (some (none,none)) (ofString "charge_gas") [.const notOpcodeFee]) 1 := by
 apply ProgBounded.weaken
 · vm_bound [vmBound_charge_gas]
 · decide
theorem not_opcode_body_bounded
 (s : PanSemStateFiniteExact 64 Guest.HostMemory)
 (upper : Nat) (current : InterpreterFundingFrame) (ancestors : List InterpreterFundingFrame)
 (layout : InterpreterFundingLayout s current.address.toNat upper (current::ancestors))
 (words : EvmMemoryOperandWords) (valid : EvmMemoryOperandAt s current.address words)
 (code : s.code=originalRuntimeCode) (budget : notOpcodeSourceCost≤s.clock) :
 RunBounded s notOpcodeBody notOpcodeSourceCost := by
 change RunBounded s notOpcodeBody (1+(1+(1+2)))
 rw [source_not_opcode_body,source_not_opcode_0]
 apply runBounded_stack_pop_physical_declaration s upper current ancestors layout words valid _ _ _ code budget
 intro a b c d first xAt xKept positive firstValid firstLayout firstCode firstBudget
 have decrement : (words.stackSize-1#64).toNat=words.stackSize.toNat-1 := BitVec.toNat_sub_of_le (BitVec.le_def.mpr (by change (1#64).toNat≤words.stackSize.toNat;change 1≤words.stackSize.toNat;exact positive))
 have inside : (words.stackSize-1#64).toNat<words.stackCapacity.toNat := by
  rw [decrement]
  have previous:=valid.stackSizeBound
  change words.stackSize.toNat≤words.stackCapacity.toNat at previous
  omega
 rw [source_not_opcode_1]
 apply RunBounded.seq (a:=1) (b:=1+2)
 · exact RunBounded.ofProg not_charge_bounded firstCode (by omega)
 · exact firstBudget
 · intro next normal keptCode nextBudget
   have args : evalListHOLFinite first (h:=fun a=>Classical.propDecidable (first.memaddrs a)) [.const notOpcodeFee]=some [.val (.word notOpcodeFee)] := rfl
   have feePositive : 0<notOpcodeFee.toNat := by decide
   obtain ⟨enough,physical,paid,progress,locals,globals,domain,endian,installed,memory⟩:=charge_gas_discard_normal_physical_context first next upper current ancestors firstLayout _ firstValid (.const notOpcodeFee) notOpcodeFee args feePositive firstCode normal
   exact not_push_tail_bounded next current.address _ physical inside (keptCode.trans firstCode) nextBudget
#print axioms not_opcode_body_bounded
end InitECandidate.Runtime
