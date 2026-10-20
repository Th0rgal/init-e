import InitECandidate.Runtime.EvmMemoryOperandHeaderTransport
import InitECandidate.Runtime.U256StoreDiscardUpperFrame
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
/-- Actual original U256 writer retains the complete physical memory/operand
context once its real charged destination span ends below scratch. -/
theorem u256_store_discard_normal_physical_context {F : Type}
 (s post : PanSemStateFiniteExact 64 F) (frame : BitVec 64)
 (words : EvmMemoryOperandWords) (valid : EvmMemoryOperandAt s frame words)
 (arguments : List (ExpHOL 64)) (a b c d destination : BitVec 64)
 (args : evalListHOLFinite s (h:=fun x=>Classical.propDecidable (s.memaddrs x)) arguments=some [fundingU256 a b c d,.val (.word destination)])
 (extent : destination.toNat+32≤words.scratchPointer.toNat)
 (code : s.code=originalRuntimeCode) (domain : DomOK s.memaddrs)
 (run : evaluateHOLFiniteState s (.call (some (none,none)) (ofString "u256_to_be32") arguments)=(none,post)) :
 EvmMemoryOperandAt post frame words ∧post.globals=s.globals ∧post.locals=s.locals ∧post.memaddrs=s.memaddrs ∧post.be=s.be ∧post.code=s.code ∧
 (∀watched : BitVec 64,words.scratchPointer.toNat≤watched.toNat→post.memory watched=s.memory watched) := by
 have cap : words.scratchPointer.toNat≤2^64 := by have bound:=words.scratchPointer.isLt;omega
 have kept (watched : BitVec 64) (above : words.scratchPointer.toNat≤watched.toNat) :=u256_store_discard_normal_upper s post arguments a b c d destination watched words.scratchPointer.toNat args extent cap above code domain run
 obtain ⟨_,globals,locals⟩:=kept frame valid.scratch_before_frame
 have metadata:=evaluateHOLFiniteState_metadata s (.call (some (none,none)) (ofString "u256_to_be32") arguments)
 rw [run] at metadata
 refine ⟨?_,globals,locals,metadata.2.1,metadata.2.2.1,metadata.1,fun watched above=>(kept watched above).1⟩
 apply EvmMemoryOperandAt.after_header_frame (post:=post) valid globals _ metadata.2.1
 intro offset member
 have small : offset.toNat<280 := by
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl|rfl|rfl|rfl|rfl|rfl|rfl <;>decide
 have natural : (frame+offset).toNat=frame.toNat+offset.toNat:=BitVec.toNat_add_of_lt (by have bound:=valid.frameExtent;omega)
 exact (kept (frame+offset) (by rw [natural];have bound:=valid.scratch_before_frame;omega)).1
#print axioms u256_store_discard_normal_physical_context
end InitECandidate.Runtime
