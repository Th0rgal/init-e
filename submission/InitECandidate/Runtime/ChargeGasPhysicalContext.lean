import InitECandidate.Runtime.ChargeGasDiscardNormalFunding
import InitECandidate.Runtime.EvmMemoryOperandHeaderTransport
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
private theorem charge_physical_header_ne (offset target : BitVec 64)
 (member : offset∈([0,8,16,24,32,40,232] : List (BitVec 64)))
 (targetMember : target∈([64,184] : List (BitVec 64))) : offset≠target := by
 simp only [List.mem_cons,List.not_mem_nil,or_false] at member targetMember
 rcases member with rfl|rfl|rfl|rfl|rfl|rfl|rfl <;>rcases targetMember with rfl|rfl <;>decide
/-- Actual successful charge_gas changes only its two real funding words;
typed PC, operand headers, vector and workspace state remain concrete. -/
theorem charge_gas_discard_normal_physical_context
 (s post : PanSemStateFiniteExact 64 Guest.HostMemory)
 (upper : Nat) (current : InterpreterFundingFrame) (ancestors : List InterpreterFundingFrame)
 (layout : InterpreterFundingLayout s current.address.toNat upper (current::ancestors))
 (words : EvmMemoryOperandWords) (valid : EvmMemoryOperandAt s current.address words)
 (argument : ExpHOL 64) (amount : BitVec 64)
 (args : evalListHOLFinite s (h:=fun a=>Classical.propDecidable (s.memaddrs a)) [argument]=some [.val (.word amount)])
 (positive : 0<amount.toNat) (code : s.code=originalRuntimeCode)
 (run : evaluateHOLFiniteState s (.call (some (none,none)) (ofString "charge_gas") [argument])=(none,post)) :
 amount≤current.gas.left ∧EvmMemoryOperandAt post current.address words ∧
 InterpreterFundingLayout post current.address.toNat upper (current.charged amount::ancestors) ∧
 interpreterFundingUsed (current::ancestors) < interpreterFundingUsed (current.charged amount::ancestors) ∧
 post.locals=s.locals ∧post.globals=s.globals ∧post.memaddrs=s.memaddrs ∧post.be=s.be ∧post.code=s.code ∧
 (∀watched : BitVec 64,watched≠current.address+64→watched≠current.address+184→post.memory watched=s.memory watched) := by
 obtain ⟨enough,exactPost,paid,used,globals,clock,locals,upperFrame⟩:=charge_gas_discard_normal_funding s post current.address.toNat upper current ancestors layout argument amount args valid.ev code run
 have memory : ∀watched : BitVec 64,watched≠current.address+64→watched≠current.address+184→post.memory watched=s.memory watched := by
  intro watched notLeft notUsed
  change watched≠current.address+64#64 at notLeft
  change watched≠current.address+184#64 at notUsed
  rw [exactPost]
  simp [chargeGasCallPost,sourceWriteWord,notLeft,notUsed,Ne.symm notLeft,Ne.symm notUsed]
 have physical : EvmMemoryOperandAt post current.address words := by
  apply valid.after_header_frame globals
  · intro offset member
    apply memory
    · intro equal;exact (charge_physical_header_ne offset 64 member (by simp)) (add_left_cancel equal)
    · intro equal;exact (charge_physical_header_ne offset 184 member (by simp)) (add_left_cancel equal)
  · rw [exactPost];rfl
 refine ⟨enough,physical,paid,by omega,locals,globals,?_,?_,?_,memory⟩
 all_goals rw [exactPost];rfl
#print axioms charge_gas_discard_normal_physical_context
end InitECandidate.Runtime
