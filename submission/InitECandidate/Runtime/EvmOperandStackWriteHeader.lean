import InitECandidate.Runtime.EvmOperandStackFreshWriteGeometry
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000
/-- The actual four-word operand write below its owning frame retains the base
and capacity header words and advances exactly the stack counter. -/
theorem stack_push_write_header {F : Type} (s : PanSemStateFiniteExact 64 F)
 (frame base index capacity a b c d : BitVec 64)
 (inside : index.toNat+1≤capacity.toNat) (capacityBound : capacity.toNat≤1024)
 (extent : base.toNat+capacity.toNat*32≤frame.toNat)
 (frameExtent : frame.toNat+280≤33806089496) :
 (stackPushWritePost s frame base index a b c d).memory (frame+8)=s.memory (frame+8) ∧
 (stackPushWritePost s frame base index a b c d).memory (frame+232)=s.memory (frame+232) ∧
 (stackPushWritePost s frame base index a b c d).memory (frame+16)=.word (index+1#64) := by
 have above8 : frame.toNat≤(frame+8#64).toNat := by
  rw [BitVec.toNat_add_of_lt (by change frame.toNat+8<2^64;omega)];change frame.toNat≤frame.toNat+8;omega
 have above232 : frame.toNat≤(frame+232#64).toNat := by
  rw [BitVec.toNat_add_of_lt (by change frame.toNat+232<2^64;omega)];change frame.toNat≤frame.toNat+232;omega
 have n8 : frame+8#64≠frame+16#64 := by
  intro eq
  have same : (8#64)=(16#64):=add_left_cancel eq
  contradiction
 have n232 : frame+232#64≠frame+16#64 := by
  intro eq
  have same : (232#64)=(16#64):=add_left_cancel eq
  contradiction
 refine ⟨stack_push_write_suffix_frame s frame base index a b c d (frame+8) n8
  (stack_push_fresh_destinations_separate base index capacity frame _ inside capacityBound extent (by omega) above8),
  stack_push_write_suffix_frame s frame base index a b c d (frame+232) n232
  (stack_push_fresh_destinations_separate base index capacity frame _ inside capacityBound extent (by omega) above232),?_⟩
 change (if frame+16#64=frame+16#64 then HolWordLab.word (index+1#64) else _) = _
 rw [if_pos rfl]
#print axioms stack_push_write_header
end InitECandidate.Runtime
