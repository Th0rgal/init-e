import InitECandidate.Runtime.PcAddPhysicalContext
import InitECandidate.Runtime.AllocationFramedGlobals
import InitECandidate.Runtime.HtabInsertRawFrame
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
/-- Actual common memory-opcode PC increment and final return, including the
real call-clock guard and source return scope. -/
theorem pc_add_one_return_physical_context {F : Type}
 (s post : PanSemStateFiniteExact 64 F) (frame : BitVec 64)
 (words : EvmMemoryOperandWords) (valid : EvmMemoryOperandAt s frame words)
 (value : ValueHOL 64) (code : s.code=originalRuntimeCode)
 (run : evaluateHOLFiniteState s (.seq (.call (some (none,none)) (ofString "pc_add") [.const 1]) (.return (.const 0)))=(some (.returned value),post)) :
 value=.val (.word 0) ∧EvmMemoryOperandAt post frame {words with pc:=words.pc+1} ∧
 post.globals=s.globals ∧post.memaddrs=s.memaddrs ∧post.be=s.be ∧post.code=s.code ∧
 (∀watched : BitVec 64,watched≠frame+0→post.memory watched=s.memory watched) := by
 obtain ⟨next,pcRun,tail⟩:=seq_returned_of_nonreturning_first (fun v=>discard_call_not_returned s (ofString "pc_add") [.const 1] v) run
 obtain ⟨nextEqual,validNext,pcFrame⟩:=pc_add_discard_normal_physical_context s next frame words valid (.const 1) 1 (by simp [evalListHOLFinite,evalListHOLExact,evalHOLExact]) code pcRun
 change evaluateHOLFiniteState next (.return (.const (0#64)))=_ at tail
 have memory:=evaluate_readOnly_memory (.return (.const (0#64))) (by decide_cbv) next
 have globals:=evaluate_readOnly_globals (.return (.const (0#64))) (by decide_cbv) next
 have metadata:=evaluateHOLFiniteState_metadata next (.return (.const (0#64)))
 rw [tail] at memory globals metadata
 have nextGlobals : next.globals=s.globals := by rw [nextEqual];rfl
 have nextDomain : next.memaddrs=s.memaddrs := by rw [nextEqual];rfl
 have nextEndian : next.be=s.be := by rw [nextEqual];rfl
 have nextCode : next.code=s.code := by rw [nextEqual];rfl
 have zero : value=.val (.word (0#64)) := by
  rw [evaluateHOLFiniteState_return] at tail
  simp only [evalHOLExact,shapeOfHOLExact] at tail
  split at tail
  · simpa using (Prod.mk.inj tail).1.symm
  · simp at tail
 refine ⟨zero,validNext.after_context globals memory metadata.2.1,globals.trans nextGlobals,metadata.2.1.trans nextDomain,metadata.2.2.1.trans nextEndian,metadata.1.trans nextCode,?_⟩
 intro watched different
 rw [memory]
 exact pcFrame watched different
#print axioms pc_add_one_return_physical_context
end InitECandidate.Runtime
