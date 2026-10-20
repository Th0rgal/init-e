import InitECandidate.Runtime.MemoryExtensionDiscardNormalFrame
import InitECandidate.Runtime.InterpreterFundingOperandStack
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
/-- Funding words are disjoint from the two actual extend_memory header writes. -/
theorem interpreter_funding_memory_headers_distinct {F : Type} (s : PanSemStateFiniteExact 64 F)
 (lower upper : Nat) (current record : InterpreterFundingFrame) (ancestors : List InterpreterFundingFrame)
 (layout : InterpreterFundingLayout s lower upper (current::ancestors))
 (present : record∈current::ancestors) (offset header : BitVec 64)
 (member : offset∈interpreterFundingOffsets) (headerMember : header∈([32,40] : List (BitVec 64))) :
 record.address+offset≠current.address+header := by
 have offsetSmall : offset.toNat<280 := by
  simp [interpreterFundingOffsets] at member
  rcases member with rfl|rfl|rfl|rfl <;> decide
 have headerSmall : header.toNat<280 := by
  simp at headerMember
  rcases headerMember with rfl|rfl <;> decide
 rcases List.mem_cons.mp present with equal|older
 · subst record
   intro equal
   have offsets : offset=header:=add_left_cancel equal
   simp [interpreterFundingOffsets] at member
   simp at headerMember
   rcases member with rfl|rfl|rfl|rfl <;>
    rcases headerMember with rfl|rfl <;> contradiction
 · have currentAt:=layout.records current (by simp)
   have recordAt:=layout.records record (by simp [older])
   have separate:=(List.pairwise_cons.mp layout.disjoint).1 record older
   exact Ne.symm (interpreter_funding_offsets_distinct current record upper currentAt.extent recordAt.extent layout.upperBound separate header offset headerSmall offsetSmall)

theorem interpreter_funding_memory_extension_normal {F : Type} (s post : PanSemStateFiniteExact 64 F)
 (upper : Nat) (current : InterpreterFundingFrame) (ancestors : List InterpreterFundingFrame)
 (layout : InterpreterFundingLayout s current.address.toNat upper (current::ancestors))
 (arguments : List (ExpHOL 64)) (base length capacity expansion pointer scratch : BitVec 64)
 (atFrame : s.globals.lookup (ofString "ev")=some (.val (.word current.address)))
 (args : evalListHOLFinite s (h:=fun a=>Classical.propDecidable (s.memaddrs a)) arguments=some [.val (.word expansion)])
 (headerDomain : ∀offset∈([24,32,40] : List (BitVec 64)),s.memaddrs (current.address+offset))
 (baseAt : s.memory (current.address+24)=.word base) (lengthAt : s.memory (current.address+32)=.word length)
 (capacityAt : s.memory (current.address+40)=.word capacity)
 (atPointer : s.globals.lookup (ofString "frame_mem_ptr")=some (.val (.word pointer)))
 (atScratch : s.globals.lookup (ofString "scratch_ptr")=some (.val (.word scratch)))
 (lengthOrder : length.toNat≤capacity.toNat) (expansionBound : expansion.toNat<2^38)
 (oldExtent : base.toNat+capacity.toNat≤pointer.toNat) (ordered : pointer.toNat≤scratch.toNat)
 (belowFrame : scratch.toNat≤current.address.toNat) (frameExtent : current.address.toNat+280≤33806089496)
 (code : s.code=originalRuntimeCode)
 (run : evaluateHOLFiniteState s (.call (some (none,none)) (ofString "extend_memory") arguments)=(none,post)) :
 InterpreterFundingLayout post current.address.toNat upper (current::ancestors) ∧post.locals=s.locals ∧
 ∃newCapacity nextPointer : BitVec 64,
 post.memory (current.address+24)=.word base ∧post.memory (current.address+32)=.word (length+expansion) ∧post.memory (current.address+40)=.word newCapacity ∧
 (length+expansion).toNat≤newCapacity.toNat ∧base.toNat+newCapacity.toNat≤nextPointer.toNat ∧
 pointer.toNat≤nextPointer.toNat ∧nextPointer.toNat≤scratch.toNat ∧
 post.globals.lookup (ofString "ev")=some (.val (.word current.address)) ∧
 post.globals.lookup (ofString "scratch_ptr")=some (.val (.word scratch)) ∧
 post.globals.lookup (ofString "frame_mem_ptr")=some (.val (.word nextPointer)) ∧
 (∀watched : BitVec 64,scratch.toNat≤watched.toNat → watched≠current.address+32 → watched≠current.address+40 → post.memory watched=s.memory watched) ∧
 post.memaddrs=s.memaddrs ∧post.be=s.be ∧post.code=s.code := by
 have result:=memory_extension_discard_normal_frame s post arguments current.address base length capacity expansion pointer scratch atFrame args headerDomain baseAt lengthAt capacityAt atPointer atScratch lengthOrder expansionBound oldExtent ordered belowFrame frameExtent code run
 obtain ⟨locals,newCapacity,nextPointer,baseKept,lengthKept,capacityKept,lengthBound,extent,mono,within,evKept,scratchKept,pointerKept,memory,domain,endian,installed⟩:=result
 refine ⟨?_,locals,newCapacity,nextPointer,baseKept,lengthKept,capacityKept,lengthBound,extent,mono,within,evKept,scratchKept,pointerKept,memory,domain,endian,installed⟩
 constructor
 · exact layout.upperBound
 · intro record present
   have recordAt:=layout.records record present
   apply recordAt.after_frame domain
   intro offset member
   have small : offset.toNat<280 := by
    simp [interpreterFundingOffsets] at member
    rcases member with rfl|rfl|rfl|rfl <;> decide
   have natural:=interpreter_funding_offset_natural record upper recordAt.extent layout.upperBound offset small
   have above : scratch.toNat≤(record.address+offset).toNat := by
    rw [natural];have lower:=recordAt.lowerBound;omega
   exact memory (record.address+offset) above
    (interpreter_funding_memory_headers_distinct s _ upper current record ancestors layout present offset 32 member (by simp))
    (interpreter_funding_memory_headers_distinct s _ upper current record ancestors layout present offset 40 member (by simp))
 · exact layout.disjoint
 · exact layout.budget
#print axioms interpreter_funding_memory_headers_distinct
#print axioms interpreter_funding_memory_extension_normal
end InitECandidate.Runtime
