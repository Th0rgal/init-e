import InitECandidate.Runtime.BitwisePushRuntimeBound
import InitECandidate.Runtime.ChargeGasPhysicalContext
import InitECandidate.Runtime.StackPopPhysicalRuntimeBound
import InitECandidate.Runtime.VmFn_charge_gas
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
private theorem bitwise_charge_bounded (kind : BitwiseBinaryKind) : ProgBounded (.call (some (none,none)) (ofString "charge_gas") [.const (bitwiseOpcodeFee kind)]) 1 := by
 apply ProgBounded.weaken
 · vm_bound [vmBound_charge_gas]
 · decide
/-- Exact original AND/OR/XOR bodies: two real pops, literal positive charge,
the real direct struct push and real PC/return. All failed outcomes included. -/
theorem bitwise_opcode_body_bounded
 (kind : BitwiseBinaryKind) (s : PanSemStateFiniteExact 64 Guest.HostMemory)
 (upper : Nat) (current : InterpreterFundingFrame) (ancestors : List InterpreterFundingFrame)
 (layout : InterpreterFundingLayout s current.address.toNat upper (current::ancestors))
 (words : EvmMemoryOperandWords) (valid : EvmMemoryOperandAt s current.address words)
 (code : s.code=originalRuntimeCode) (budget : bitwiseOpcodeSourceCost kind≤s.clock) :
 RunBounded s (bitwiseOpcodeBody kind) (bitwiseOpcodeSourceCost kind) := by
 change RunBounded s (bitwiseOpcodeBody kind) (1+(1+(1+(1+2))))
 rw [source_bitwise_opcode_body kind,source_bitwise_opcode_0 kind]
 apply runBounded_stack_pop_physical_declaration s upper current ancestors layout words valid _ _ _ code budget
 intro a b c d first xAt xKept positive firstValid firstLayout firstCode firstBudget
 rw [source_bitwise_opcode_1 kind]
 apply runBounded_stack_pop_physical_declaration first upper current ancestors firstLayout _ firstValid _ _ _ firstCode firstBudget
 intro e f g h second yAt yKept secondPositive secondValid secondLayout secondCode secondBudget
 have decrement : ((words.stackSize-1#64)-1#64).toNat=(words.stackSize-1#64).toNat-1 := BitVec.toNat_sub_of_le (BitVec.le_def.mpr (by change (1#64).toNat≤(words.stackSize-1#64).toNat;change 1≤(words.stackSize-1#64).toNat;exact secondPositive))
 have inside : ((words.stackSize-1#64)-1#64).toNat<words.stackCapacity.toNat := by
  rw [decrement]
  have previous:=firstValid.stackSizeBound
  change (words.stackSize-1#64).toNat≤words.stackCapacity.toNat at previous
  change 0<(words.stackSize-1#64).toNat at secondPositive
  omega
 rw [source_bitwise_opcode_2 kind]
 apply RunBounded.seq (a:=1) (b:=1+2)
 · exact RunBounded.ofProg (bitwise_charge_bounded kind) secondCode (by omega)
 · exact secondBudget
 · intro next normal keptCode nextBudget
   have args : evalListHOLFinite second (h:=fun a=>Classical.propDecidable (second.memaddrs a)) [.const (bitwiseOpcodeFee kind)]=some [.val (.word (bitwiseOpcodeFee kind))] := rfl
   have feePositive : 0<(bitwiseOpcodeFee kind).toNat := by cases kind <;>decide
   obtain ⟨enough,physical,paid,progress,locals,globals,domain,endian,installed,memory⟩:=charge_gas_discard_normal_physical_context second next upper current ancestors secondLayout _ secondValid (.const (bitwiseOpcodeFee kind)) (bitwiseOpcodeFee kind) args feePositive secondCode normal
   exact bitwise_push_tail_bounded kind next current.address _ physical inside (keptCode.trans secondCode) nextBudget
#print axioms bitwise_opcode_body_bounded
end InitECandidate.Runtime
