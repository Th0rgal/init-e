import InitECandidate.Runtime.NotPushPhysicalContext
import InitECandidate.Runtime.BitwiseStructArguments
import InitECandidate.Runtime.ChargeGasPhysicalContext
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
set_option maxRecDepth 100000
set_option maxHeartbeats 6000000
private theorem funding_after_not_frame {F : Type}
 (s post : PanSemStateFiniteExact 64 F) (upper : Nat)
 (current : InterpreterFundingFrame) (ancestors : List InterpreterFundingFrame)
 (valid : InterpreterFundingLayout s current.address.toNat upper (current::ancestors))
 (domain : post.memaddrs=s.memaddrs)
 (memory : ∀watched : BitVec 64,current.address.toNat≤watched.toNat→watched≠current.address+0→watched≠current.address+16→post.memory watched=s.memory watched) :
 InterpreterFundingLayout post current.address.toNat upper (current::ancestors) := by
 have currentAt:=valid.records current (by simp)
 have counterNatural:=interpreter_funding_offset_natural current upper currentAt.extent valid.upperBound (0#64) (by decide)
 have leftNatural:=interpreter_funding_offset_natural current upper currentAt.extent valid.upperBound (16#64) (by decide)
 constructor
 · exact valid.upperBound
 · intro record member
   have old:=valid.records record member
   apply InterpreterFundingFrameAt.after_frame (post:=post) old domain
   intro offset included
   have offsetBounds : 64≤offset.toNat ∧offset.toNat<280 := by
    simp only [interpreterFundingOffsets,List.mem_cons,List.not_mem_nil,or_false] at included
    rcases included with rfl|rfl|rfl|rfl <;>decide
   have natural:=interpreter_funding_offset_natural record upper old.extent valid.upperBound offset offsetBounds.2
   apply memory (record.address+offset) (by rw [natural];have bound:=old.lowerBound;omega)
   · intro equal
     have same:=congrArg BitVec.toNat equal
     change (record.address+offset).toNat=(current.address+0#64).toNat at same
     rw [BitVec.add_zero,natural] at same
     have bound:=old.lowerBound
     omega
   · intro equal
     have same:=congrArg BitVec.toNat equal
     change (record.address+offset).toNat=(current.address+16#64).toNat at same
     rw [natural,leftNatural] at same
     change record.address.toNat+offset.toNat=current.address.toNat+16 at same
     have bound:=old.lowerBound
     omega
 · exact valid.disjoint
 · exact valid.budget
/-- Actual direct NOT charge plus push suffix, with the four complement limbs
read off the checked popped local. -/
theorem not_charged_returned_physical_context
 (s post : PanSemStateFiniteExact 64 Guest.HostMemory)
 (upper : Nat) (current : InterpreterFundingFrame) (ancestors : List InterpreterFundingFrame)
 (layout : InterpreterFundingLayout s current.address.toNat upper (current::ancestors))
 (words : EvmMemoryOperandWords) (valid : EvmMemoryOperandAt s current.address words)
 (a b c d : BitVec 64) (value : ValueHOL 64)
 (atX : s.locals.lookup (ofString "x")=some (fundingU256 a b c d))
 (inside : words.stackSize.toNat<words.stackCapacity.toNat)
 (fullDomain : ∀address : BitVec 64,address.toNat<33806089496→s.memaddrs address)
 (code : s.code=originalRuntimeCode)
 (run : evaluateHOLFiniteState s (notOpcodeAt 1)=(some (.returned value),post)) :
 value=.val (.word 0) ∧notOpcodeFee≤current.gas.left ∧
 InterpreterFundingLayout post current.address.toNat upper (current.charged notOpcodeFee::ancestors) ∧
 interpreterFundingUsed (current::ancestors) < interpreterFundingUsed (current.charged notOpcodeFee::ancestors) ∧
 EvmMemoryOperandAt post current.address {words with pc:=words.pc+1,stackSize:=words.stackSize+1} ∧
 post.globals=s.globals ∧post.memaddrs=s.memaddrs ∧post.be=s.be ∧post.code=s.code ∧
 (∀watched : BitVec 64,current.address.toNat≤watched.toNat→watched≠current.address+0→watched≠current.address+16→watched≠current.address+64→watched≠current.address+184→post.memory watched=s.memory watched) := by
 rw [source_not_opcode_1] at run
 obtain ⟨next,charged,tail⟩:=seq_returned_of_nonreturning_first (fun v=>discard_call_not_returned s (ofString "charge_gas") [.const notOpcodeFee] v) run
 obtain ⟨enough,physical,paid,progress,locals,globals,domain,endian,installed,chargeFrame⟩:=charge_gas_discard_normal_physical_context s next upper current ancestors layout words valid (.const notOpcodeFee) notOpcodeFee rfl (by decide) code charged
 obtain ⟨zero,finalPhysical,finalGlobals,finalDomain,finalEndian,finalCode,pushFrame⟩:=not_push_returned_physical_context next post current.address words physical (notLimb a) (notLimb b) (notLimb c) (notLimb d) value (not_push_args_of_locals next a b c d (by rw [locals];exact atX)) inside (by intro address below;rw [domain];exact fullDomain address below) (installed.trans code) tail
 have finalFunding:=funding_after_not_frame next post upper (current.charged notOpcodeFee) ancestors paid finalDomain pushFrame
 refine ⟨zero,enough,finalFunding,progress,finalPhysical,finalGlobals.trans globals,finalDomain.trans domain,finalEndian.trans endian,finalCode.trans installed,?_⟩
 intro watched above notPc notCounter notLeft notUsed
 rw [pushFrame watched above notPc notCounter]
 exact chargeFrame watched notLeft notUsed
#print axioms not_charged_returned_physical_context
end InitECandidate.Runtime
