import InitECandidate.Runtime.EvmOperandStackProtected
import InitECandidate.Runtime.InterpreterFundingLayout
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

theorem interpreter_funding_stack_headers_distinct {F : Type} (s : PanSemStateFiniteExact 64 F)
 (lower upper : Nat) (current record : InterpreterFundingFrame) (ancestors : List InterpreterFundingFrame)
 (layout : InterpreterFundingLayout s lower upper (current::ancestors))
 (present : record∈current::ancestors) (offset header : BitVec 64)
 (member : offset∈interpreterFundingOffsets) (headerMember : header∈([8,16,232] : List (BitVec 64))) :
 record.address+offset≠current.address+header := by
 have offsetSmall : offset.toNat<280 := by
  simp [interpreterFundingOffsets] at member
  rcases member with rfl|rfl|rfl|rfl <;> decide
 have headerSmall : header.toNat<280 := by
  simp at headerMember
  rcases headerMember with rfl|rfl|rfl <;> decide
 rcases List.mem_cons.mp present with equal|older
 · subst record
   intro equal
   have offsets : offset=header:=add_left_cancel equal
   simp [interpreterFundingOffsets] at member
   simp at headerMember
   rcases member with rfl|rfl|rfl|rfl <;>
    rcases headerMember with rfl|rfl|rfl <;> contradiction
 · have currentAt:=layout.records current (by simp)
   have recordAt:=layout.records record (by simp [older])
   have separate:=(List.pairwise_cons.mp layout.disjoint).1 record older
   exact Ne.symm (interpreter_funding_offsets_distinct current record upper currentAt.extent recordAt.extent layout.upperBound separate header offset headerSmall offsetSmall)

/-- Actual whole stack_push preserves all live frame funding words and their
concrete physical registry. Operand buffer ownership/capacity is explicit;
no runtime or frame callback is used. -/
theorem interpreter_funding_stack_push_returned {F : Type} (s post : PanSemStateFiniteExact 64 F)
 (upper : Nat) (current : InterpreterFundingFrame) (ancestors : List InterpreterFundingFrame)
 (layout : InterpreterFundingLayout s current.address.toNat upper (current::ancestors))
 (base index capacity scratch frontier a b c d : BitVec 64) (value : ValueHOL 64)
 (atCurrent : s.globals.lookup (ofString "ev")=some (.val (.word current.address)))
 (atValue : s.locals.lookup (ofString "v")=some (fundingU256 a b c d))
 (headerDomain : ∀offset∈([8,16,232] : List (BitVec 64)),s.memaddrs (current.address+offset))
 (baseAt : s.memory (current.address+8)=.word base) (indexAt : s.memory (current.address+16)=.word index)
 (capacityAt : s.memory (current.address+232)=.word capacity)
 (positive : 1≤capacity.toNat) (capacityBound : capacity.toNat≤1024) (indexBound : index.toNat≤capacity.toNat)
 (bufferExtent : base.toNat+capacity.toNat*32≤current.address.toNat)
 (atScratch : s.globals.lookup (ofString "scratch_ptr")=some (.val (.word scratch)))
 (atFrontier : s.globals.lookup (ofString "frame_mem_ptr")=some (.val (.word frontier)))
 (ordered : frontier≤scratch) (scratchBeforeFrame : scratch.toNat≤current.address.toNat)
 (frameExtent : current.address.toNat+280≤33806089496)
 (fullDomain : ∀address : BitVec 64,address.toNat<33806089496 → s.memaddrs address)
 (code : s.code=originalRuntimeCode)
 (run : evaluateHOLFiniteState s (stackPushAt 0)=(some (.returned value),post)) :
 value=.val (.word 0) ∧InterpreterFundingLayout post current.address.toNat upper (current::ancestors) ∧
 ∃nextScratch : BitVec 64,
 post.globals.lookup (ofString "scratch_ptr")=some (.val (.word nextScratch)) ∧
 nextScratch.toNat≤scratch.toNat ∧
 post.globals.lookup (ofString "frame_mem_ptr")=some (.val (.word frontier)) ∧
 post.globals.lookup (ofString "ev")=some (.val (.word current.address)) := by
 have safe (record : InterpreterFundingFrame) (present : record∈current::ancestors)
  (offset : BitVec 64) (member : offset∈interpreterFundingOffsets) := by
  have recordAt:=layout.records record present
  have small : offset.toNat<280 := by
   simp [interpreterFundingOffsets] at member
   rcases member with rfl|rfl|rfl|rfl <;> decide
  have natural:=interpreter_funding_offset_natural record upper recordAt.extent layout.upperBound offset small
  have above : current.address.toNat≤(record.address+offset).toNat := by rw [natural];have lower:=recordAt.lowerBound;omega
  exact stack_push_protected_returned s post current.address base index capacity scratch frontier a b c d (record.address+offset) value
   atCurrent atValue headerDomain baseAt indexAt capacityAt positive capacityBound indexBound bufferExtent atScratch atFrontier
   ordered scratchBeforeFrame frameExtent fullDomain above
   (interpreter_funding_stack_headers_distinct s _ upper current record ancestors layout present offset 8 member (by simp))
   (interpreter_funding_stack_headers_distinct s _ upper current record ancestors layout present offset 16 member (by simp))
   (interpreter_funding_stack_headers_distinct s _ upper current record ancestors layout present offset 232 member (by simp)) code run
 obtain ⟨returned,memory,domain,endian,installed,globals⟩:=safe current (by simp) 64 (by simp [interpreterFundingOffsets])
 refine ⟨returned,?_,globals⟩
 constructor
 · exact layout.upperBound
 · intro record present
   apply (layout.records record present).after_frame domain
   intro offset member
   exact (safe record present offset member).2.1
 · exact layout.disjoint
 · exact layout.budget
#print axioms interpreter_funding_stack_headers_distinct
#print axioms interpreter_funding_stack_push_returned
end InitECandidate.Runtime
