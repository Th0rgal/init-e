import InitECandidate.Runtime.HtrU64AtBound
import InitECandidate.Runtime.MemzeroNormalFrame
import InitECandidate.Runtime.MemcpyCallMemory
import InitECandidate.Runtime.MemcpyIntervalFrame
import InitECandidate.Runtime.MarkedHeapReturn
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

theorem htrU64At_body_returned_memory {F : Type} (state post : PanSemStateFiniteExact 64 F)
    (p out watched : BitVec 64) (value : ValueHOL 64)
    (hp : state.locals.lookup (ofString "p") = some (.val (.word p)))
    (ho : state.locals.lookup (ofString "out") = some (.val (.word out)))
    (code : state.code = originalRuntimeCode) (aligned : out.toNat % 8 = 0)
    (fits : out.toNat + 32 ≤ 33806089496)
    (outside : watched.toNat < out.toNat ∨ out.toNat + 32 ≤ watched.toNat)
    (budget : 29 ≤ state.clock)
    (run : evaluateHOLFiniteState state (sourceFunctionBody Guest.guestFn_htr_u64_at) = (some (.returned value),post)) :
    post.memory watched = state.memory watched := by
  rw [sourceFunctionBody_eq_structural] at run
  change evaluateHOLFiniteState state (.seq
    (.call (some (none,none)) (ofString "memzero") [.var .local (ofString "out"),.const 32])
    (.seq (.call (some (none,none)) (ofString "memcpy") [.var .local (ofString "out"),.var .local (ofString "p"),.const 8])
      (.return (.const 0)))) = _ at run
  obtain ⟨middle,zero,rest⟩ := seq_returned_of_nonreturning_first
    (fun v => evaluate_noDirectReturnWhile _ (by decide) state v) run
  have zeroFrame := memzero_call_normal_memory state middle _ out 32 watched
    (by simp [evalListHOLExact,evalHOLExact,ho]) code aligned fits outside zero
  have kept (key : MlS) : middle.locals.lookup key = state.locals.lookup key := by
    rw [zeroFrame.2]
  have middleCode := evaluateHOLFiniteState_metadata state
    (.call (some (none,none)) (ofString "memzero") [.var .local (ofString "out"),.const 32])
  rw [zero] at middleCode
  have zeroBound := (memzero_const_progBounded (.var .local (ofString "out")) 32 (by decide)) state code (by change 16 ≤ state.clock; omega)
  rw [zero] at zeroBound
  have enough : 12 ≤ middle.clock := by
    have spent : state.clock ≤ middle.clock + 16 := zeroBound.1
    omega
  obtain ⟨copied,copy,returned⟩ := seq_returned_of_nonreturning_first
    (fun v => evaluate_noDirectReturnWhile _ (by decide) middle v) rest
  have separation := memcpy_interval_separate out (32#64) watched aligned fits outside
  have copyFrame := memcpy_call_normal_memory middle copied _ out p 8 watched
    (by simp [evalListHOLExact,evalHOLExact,kept,ho,hp]) (middleCode.1.trans code)
    (fun offset inside => (separation offset (by change offset < 32; change offset < 8 at inside; omega)).1)
    (fun offset inside => (separation offset (by change offset < 32; change offset < 8 at inside; omega)).2)
    (by decide) enough copy
  have finalMemory := evaluate_readOnly_memory (.return (.const 0)) rfl copied
  rw [returned] at finalMemory
  rw [finalMemory,copyFrame,zeroFrame.1]

theorem htrU64At_call_normal_memory {F : Type} (state post : PanSemStateFiniteExact 64 F)
    (arguments : List (ExpHOL 64)) (p out watched : BitVec 64)
    (args : evalListHOLFinite state (h := fun a => Classical.propDecidable (state.memaddrs a)) arguments =
      some [.val (.word p),.val (.word out)])
    (code : state.code = originalRuntimeCode) (aligned : out.toNat % 8 = 0)
    (fits : out.toNat + 32 ≤ 33806089496)
    (outside : watched.toNat < out.toNat ∨ out.toNat + 32 ≤ watched.toNat)
    (budget : 30 ≤ state.clock)
    (run : evaluateHOLFiniteState state (.call (some (none,none)) (ofString "htr_u64_at") arguments) = (none,post)) :
    post.memory watched = state.memory watched := by
  have installed : state.code.lookup (ofString "htr_u64_at") =
      some ([(ofString "p",.one),(ofString "out",.one)],sourceFunctionBody Guest.guestFn_htr_u64_at,.one) := by
    rw [code]; exact originalRuntimeCode_htrU64At_lookup
  have lookup := pan_two_word_lookup state.code.lookup (ofString "htr_u64_at") (ofString "p") (ofString "out")
    (sourceFunctionBody Guest.guestFn_htr_u64_at) p out (by decide) installed
  obtain ⟨value,output,bodyRun,_,postEq⟩ := evaluate_discardCall_normal_result state post (ofString "htr_u64_at")
    .one arguments _ _ _ args lookup run
  rw [postEq]
  let entry := callEntryStateHOLFinite state
    ((HolFiniteMapExact.empty.update (ofString "p",.val (.word p))).update (ofString "out",.val (.word out)))
  exact htrU64At_body_returned_memory entry output p out watched value
    (by simp (config := {decide := true}) [entry,callEntryStateHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE])
    (by simp [entry,callEntryStateHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE])
    code aligned fits outside (by change 29 ≤ state.clock - 1; omega) bodyRun

#print axioms htrU64At_body_returned_memory
#print axioms htrU64At_call_normal_memory
end InitECandidate.Runtime
