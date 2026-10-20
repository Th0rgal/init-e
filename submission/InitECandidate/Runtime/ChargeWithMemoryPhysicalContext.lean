import InitECandidate.Runtime.EvmMemoryOperandContext
import InitECandidate.Runtime.ChargeWithMemoryDiscardUpperFrame
import InitECandidate.Runtime.ChargeWithMemoryDiscardAccessProgress
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
set_option maxRecDepth 100000
set_option maxHeartbeats 6000000
private theorem charged_physical_header_offsets_ne (left right : BitVec 64)
 (leftMember : left∈([0,8,16,232] : List (BitVec 64)))
 (rightMember : right∈([32,40,64,184] : List (BitVec 64))) : left≠right := by
 simp only [List.mem_cons,List.not_mem_nil,or_false] at leftMember rightMember
 rcases leftMember with rfl|rfl|rfl|rfl <;>rcases rightMember with rfl|rfl|rfl|rfl <;>decide
/-- Real charged-memory call closes the whole concrete memory/operand context,
not only funding. The same run supplies the span used by real memory writes. -/
theorem charge_with_memory_discard_physical_context
 (s post : PanSemStateFiniteExact 64 Guest.HostMemory) (upper : Nat)
 (current : InterpreterFundingFrame) (ancestors : List InterpreterFundingFrame)
 (layout : InterpreterFundingLayout s current.address.toNat upper (current::ancestors))
 (words : EvmMemoryOperandWords) (valid : EvmMemoryOperandAt s current.address words)
 (arguments : List (ExpHOL 64)) (gasBase sa sb sc sd na nb nc nd : BitVec 64)
 (args : evalListHOLFinite s (h:=fun a=>Classical.propDecidable (s.memaddrs a)) arguments=some [.val (.word gasBase),fundingU256 sa sb sc sd,fundingU256 na nb nc nd])
 (positive : 0<gasBase.toNat) (code : s.code=originalRuntimeCode)
 (run : evaluateHOLFiniteState s (.call (some (none,none)) (ofString "charge_with_memory") arguments)=(none,post)) :
 post.locals=s.locals ∧∃expansion total newCapacity nextPointer : BitVec 64,
 gasBase.toNat≤total.toNat ∧total≤current.gas.left ∧
 InterpreterFundingLayout post current.address.toNat upper (current.charged total::ancestors) ∧
 interpreterFundingUsed (current::ancestors) < interpreterFundingUsed (current.charged total::ancestors) ∧
 EvmMemoryOperandAt post current.address {words with memoryLength:=words.memoryLength+expansion,memoryCapacity:=newCapacity,framePointer:=nextPointer} ∧
 (evmSatWord na nb nc nd≠0#64→(evmSatWord sa sb sc sd).toNat+(evmSatWord na nb nc nd).toNat≤(words.memoryLength+expansion).toNat) ∧
 (∀watched : BitVec 64,words.scratchPointer.toNat≤watched.toNat→watched≠current.address+32→watched≠current.address+40→watched≠current.address+64→watched≠current.address+184→post.memory watched=s.memory watched) := by
 have headerDomain : ∀offset∈([24,32,40] : List (BitVec 64)),s.memaddrs (current.address+offset) := by
  intro offset member;exact valid.headerDomain offset (by simp only [List.mem_cons,List.not_mem_nil,or_false] at member ⊢;tauto)
 have below:=valid.scratch_before_frame
 obtain ⟨locals,expansion,total,small,baseBound,enough,paid,used,progress,newCapacity,nextPointer,baseKept,lengthKept,capacityKept,lengthBound,newAligned,access,extent,mono,within,evKept,scratchKept,pointerKept,domain,endian,installed⟩:=charge_with_memory_discard_access_progress s post upper current ancestors layout arguments words.memoryBase words.memoryLength words.memoryCapacity words.framePointer words.scratchPointer gasBase sa sb sc sd na nb nc nd args valid.memoryAligned positive valid.ev headerDomain valid.memoryBase valid.memoryLength valid.memoryCapacity valid.framePointer valid.scratchPointer valid.memoryLengthBound valid.memoryExtent valid.pointers below valid.frameExtent code run
 have upperFrame (watched : BitVec 64) (above : words.scratchPointer.toNat≤watched.toNat)
  (notLength : watched≠current.address+32) (notCapacity : watched≠current.address+40)
  (notLeft : watched≠current.address+64) (notUsed : watched≠current.address+184) : post.memory watched=s.memory watched := by
  exact charge_with_memory_discard_upper_frame s post upper current ancestors layout arguments (fundingU256 sa sb sc sd) (fundingU256 na nb nc nd) words.memoryBase words.memoryLength words.memoryCapacity words.framePointer words.scratchPointer gasBase watched args (by simp [fundingU256,shapeOfHOLExact]) (by simp [fundingU256,shapeOfHOLExact]) valid.ev headerDomain valid.memoryBase valid.memoryLength valid.memoryCapacity valid.framePointer valid.scratchPointer valid.memoryLengthBound valid.memoryExtent valid.pointers below valid.frameExtent above notLength notCapacity notLeft notUsed code run
 have keep (offset : BitVec 64) (member : offset∈([0,8,16,232] : List (BitVec 64))) : post.memory (current.address+offset)=s.memory (current.address+offset) := by
  have small : offset.toNat<280 := by simp only [List.mem_cons,List.not_mem_nil,or_false] at member;rcases member with rfl|rfl|rfl|rfl <;>decide
  have natural:=interpreter_funding_offset_natural current 33806089496 valid.frameExtent (by decide) offset small
  apply upperFrame (current.address+offset) (by rw [natural];omega)
  all_goals intro equal;exact (charged_physical_header_offsets_ne offset _ member (by simp)) (add_left_cancel equal)
 refine ⟨locals,expansion,total,newCapacity,nextPointer,baseBound,enough,paid,progress,?_,access,upperFrame⟩
 constructor
 · exact evKept
 · exact pointerKept
 · exact scratchKept
 · intro offset member;rw [domain];exact valid.headerDomain offset member
 · exact (keep 0 (by simp)).trans valid.pc
 · exact (keep 8 (by simp)).trans valid.stackBase
 · exact (keep 16 (by simp)).trans valid.stackSize
 · exact (keep 232 (by simp)).trans valid.stackCapacity
 · exact baseKept
 · exact lengthKept
 · exact capacityKept
 · exact valid.stackCapacityPositive
 · exact valid.stackCapacityBound
 · exact valid.stackSizeBound
 · exact valid.stackLower
 · exact valid.stackExtent
 · exact newAligned
 · exact lengthBound
 · exact extent
 · exact within
 · exact valid.frameExtent
#print axioms charge_with_memory_discard_physical_context
end InitECandidate.Runtime
