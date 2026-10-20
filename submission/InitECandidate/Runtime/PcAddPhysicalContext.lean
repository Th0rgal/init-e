import InitECandidate.Runtime.EvmMemoryOperandContext
import InitECandidate.Runtime.PcAddCall
import InitECandidate.Runtime.VmFn_pc_add
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
/-- Actual installed PC update retains the complete physical memory/operand
context and every other word, with no call-clock/success premise. -/
theorem pc_add_discard_normal_physical_context {F : Type}
 (s post : PanSemStateFiniteExact 64 F) (frame : BitVec 64)
 (words : EvmMemoryOperandWords) (valid : EvmMemoryOperandAt s frame words)
 (argument : ExpHOL 64) (amount : BitVec 64)
 (args : evalListHOLFinite s (h:=fun a=>Classical.propDecidable (s.memaddrs a)) [argument]=some [.val (.word amount)])
 (code : s.code=originalRuntimeCode)
 (run : evaluateHOLFiniteState s (.call (some (none,none)) (ofString "pc_add") [argument])=(none,post)) :
 post=pcAddCallPost s frame words.pc amount ∧
 EvmMemoryOperandAt post frame {words with pc:=words.pc+amount} ∧
 (∀watched : BitVec 64,watched≠frame+0→post.memory watched=s.memory watched) := by
 have installed : s.code.lookup (ofString "pc_add")=some ([(ofString "n",.one)],sourceFunctionBody Guest.guestFn_pc_add,.one) := by rw [code];exact vmLookup_pc_add
 have lookup:=pan_single_word_lookup s.code.lookup (ofString "pc_add") (ofString "n") (sourceFunctionBody Guest.guestFn_pc_add) amount installed
 have clock : s.clock≠0 := by
  intro zero
  rw [evaluateHOLFiniteState_call,args] at run
  simp only at run
  rw [lookup] at run
  simp [zero] at run
 have exactCall:=evaluate_pcAdd_call s argument frame words.pc amount args installed clock valid.ev (valid.headerDomain 0 (by simp)) valid.pc
 have equal : post=pcAddCallPost s frame words.pc amount:=(Prod.mk.inj (run.symm.trans exactCall)).2
 subst post
 have keep (watched : BitVec 64) (different : watched≠frame+0#64) : (pcAddCallPost s frame words.pc amount).memory watched=s.memory watched := by
  change (if watched=frame+0#64 then _ else _)=_
  rw [if_neg different]
 refine ⟨rfl,?_,keep⟩
 constructor
 · exact valid.ev
 · exact valid.framePointer
 · exact valid.scratchPointer
 · exact valid.headerDomain
 · simp [pcAddCallPost,sourceWriteWord]
 · exact (keep (frame+8) (by intro equal;exact (by decide : (8#64)≠0#64) (add_left_cancel equal))).trans valid.stackBase
 · exact (keep (frame+16) (by intro equal;exact (by decide : (16#64)≠0#64) (add_left_cancel equal))).trans valid.stackSize
 · exact (keep (frame+232) (by intro equal;exact (by decide : (232#64)≠0#64) (add_left_cancel equal))).trans valid.stackCapacity
 · exact (keep (frame+24) (by intro equal;exact (by decide : (24#64)≠0#64) (add_left_cancel equal))).trans valid.memoryBase
 · exact (keep (frame+32) (by intro equal;exact (by decide : (32#64)≠0#64) (add_left_cancel equal))).trans valid.memoryLength
 · exact (keep (frame+40) (by intro equal;exact (by decide : (40#64)≠0#64) (add_left_cancel equal))).trans valid.memoryCapacity
 · exact valid.stackCapacityPositive
 · exact valid.stackCapacityBound
 · exact valid.stackSizeBound
 · exact valid.stackLower
 · exact valid.stackExtent
 · exact valid.memoryAligned
 · exact valid.memoryLengthBound
 · exact valid.memoryExtent
 · exact valid.pointers
 · exact valid.frameExtent
#print axioms pc_add_discard_normal_physical_context
end InitECandidate.Runtime
