import InitECandidate.Runtime.EvmMemoryOperandHeaderTransport
import InitECandidate.Runtime.MemzeroNormalFrame
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
/-- Actual byte-store access below scratch keeps the entire concrete physical
context and every old operand/control word at or above scratch. -/
theorem store_byte_normal_physical_context {F : Type}
 (s post : PanSemStateFiniteExact 64 F) (frame : BitVec 64)
 (words : EvmMemoryOperandWords) (valid : EvmMemoryOperandAt s frame words)
 (destination expression : ExpHOL 64) (address value : BitVec 64)
 (below : address.toNat<words.scratchPointer.toNat)
 (addressEval : @evalHOLExact 64 F _ s.toExact (fun a=>Classical.propDecidable (s.memaddrs a)) destination=some (.val (.word address)))
 (valueEval : @evalHOLExact 64 F _ s.toExact (fun a=>Classical.propDecidable (s.memaddrs a)) expression=some (.val (.word value)))
 (run : evaluateHOLFiniteState s (.storeByte destination expression)=(none,post)) :
 EvmMemoryOperandAt post frame words ∧post.globals=s.globals ∧post.locals=s.locals ∧post.memaddrs=s.memaddrs ∧post.be=s.be ∧post.code=s.code ∧
 (∀watched : BitVec 64,words.scratchPointer.toNat≤watched.toNat→post.memory watched=s.memory watched) := by
 obtain ⟨cell,rfl⟩:=storeByte_normal s post destination expression address value addressEval valueEval run
 have keptUpper (watched : BitVec 64) (above : words.scratchPointer.toNat≤watched.toNat) : (sourceWriteByte s address value cell).memory watched=s.memory watched := by
  apply sourceWriteByte_memory_other
  intro same
  have aligned : (panByteAlignHOL address).toNat≤address.toNat := by rw [byteAlign_toNat];exact Nat.div_mul_le_self _ _
  have equal:=congrArg BitVec.toNat same
  omega
 refine ⟨?_,rfl,rfl,rfl,rfl,rfl,keptUpper⟩
 apply EvmMemoryOperandAt.after_header_frame (post:=sourceWriteByte s address value cell) valid rfl _ rfl
 intro offset member
 have small : offset.toNat<280 := by
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl|rfl|rfl|rfl|rfl|rfl|rfl <;>decide
 have natural : (frame+offset).toNat=frame.toNat+offset.toNat := BitVec.toNat_add_of_lt (by have bound:=valid.frameExtent;omega)
 apply keptUpper
 rw [natural]
 have frameBound:=valid.scratch_before_frame
 omega
#print axioms store_byte_normal_physical_context
end InitECandidate.Runtime
