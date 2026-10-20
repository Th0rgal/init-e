import InitECandidate.Runtime.ArithmeticHelperRuntimeBound
import InitECandidate.Runtime.ChargeGasPhysicalContext
import InitECandidate.Runtime.StackPopPhysicalRuntimeBound
import InitECandidate.Runtime.VmFn_charge_gas
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
def arithmeticOpcodeSourceCost (kind : ArithmeticOpcodeKind) : Nat:=1+(1+(1+(arithmeticOpcodeHelperCost kind+1+2)))
private theorem arithmetic_charge_bounded (kind : ArithmeticOpcodeKind) : ProgBounded (.call (some (none,none)) (ofString "charge_gas") [.const (arithmeticOpcodeFee kind)]) 1 := by
 apply ProgBounded.weaken
 · vm_bound [vmBound_charge_gas]
 · decide
/-- Exact original ADD/SUB/MUL bodies: two real pops, literal positive charge,
actual pure helper and real nongrowing push/PC. All failed outcomes included. -/
theorem arithmetic_opcode_body_bounded
 (kind : ArithmeticOpcodeKind) (s : PanSemStateFiniteExact 64 Guest.HostMemory)
 (upper : Nat) (current : InterpreterFundingFrame) (ancestors : List InterpreterFundingFrame)
 (layout : InterpreterFundingLayout s current.address.toNat upper (current::ancestors))
 (words : EvmMemoryOperandWords) (valid : EvmMemoryOperandAt s current.address words)
 (code : s.code=originalRuntimeCode) (budget : arithmeticOpcodeSourceCost kind≤s.clock) :
 RunBounded s (arithmeticOpcodeBody kind) (arithmeticOpcodeSourceCost kind) := by
 change RunBounded s (arithmeticOpcodeBody kind) (1+(1+(1+(arithmeticOpcodeHelperCost kind+1+2))))
 rw [source_arithmetic_opcode_body kind,source_arithmetic_opcode_0 kind]
 apply runBounded_stack_pop_physical_declaration s upper current ancestors layout words valid _ _ _ code budget
 intro a b c d first xAt xKept positive firstValid firstLayout firstCode firstBudget
 rw [source_arithmetic_opcode_1 kind]
 apply runBounded_stack_pop_physical_declaration first upper current ancestors firstLayout _ firstValid _ _ _ firstCode firstBudget
 intro e f g h second yAt yKept secondPositive secondValid secondLayout secondCode secondBudget
 have decrement : ((words.stackSize-1#64)-1#64).toNat=(words.stackSize-1#64).toNat-1 := BitVec.toNat_sub_of_le (BitVec.le_def.mpr (by change (1#64).toNat≤(words.stackSize-1#64).toNat;change 1≤(words.stackSize-1#64).toNat;exact secondPositive))
 have inside : ((words.stackSize-1#64)-1#64).toNat<words.stackCapacity.toNat := by
  rw [decrement]
  have previous:=firstValid.stackSizeBound
  change (words.stackSize-1#64).toNat≤words.stackCapacity.toNat at previous
  change 0<(words.stackSize-1#64).toNat at secondPositive
  omega
 rw [source_arithmetic_opcode_2 kind]
 apply RunBounded.seq (a:=1) (b:=arithmeticOpcodeHelperCost kind+1+2)
 · exact RunBounded.ofProg (arithmetic_charge_bounded kind) secondCode (by omega)
 · exact secondBudget
 · intro next normal keptCode nextBudget
   have args : evalListHOLFinite second (h:=fun a=>Classical.propDecidable (second.memaddrs a)) [.const (arithmeticOpcodeFee kind)]=some [.val (.word (arithmeticOpcodeFee kind))] := rfl
   have feePositive : 0<(arithmeticOpcodeFee kind).toNat := by cases kind <;>decide
   obtain ⟨enough,physical,paid,progress,locals,globals,domain,endian,installed,memory⟩:=charge_gas_discard_normal_physical_context second next upper current ancestors secondLayout _ secondValid (.const (arithmeticOpcodeFee kind)) (arithmeticOpcodeFee kind) args feePositive secondCode normal
   exact arithmetic_helper_tail_bounded kind next current.address _ physical inside (keptCode.trans secondCode) nextBudget
#print axioms arithmetic_opcode_body_bounded
end InitECandidate.Runtime
