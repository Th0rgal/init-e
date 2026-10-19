import InitECandidate.Runtime.HtrBytesVectorShortBound
import InitECandidate.Runtime.MemzeroNormalFrame
import InitECandidate.Runtime.MemcpyCallMemory
import InitECandidate.Runtime.MemcpyIntervalFrame
import InitECandidate.Runtime.HtabGrowFrame
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

theorem htrBytesVector_short_returned_memory {F : Type} (state post : PanSemStateFiniteExact 64 F)
    (p n out watched : BitVec 64) (value : ValueHOL 64)
    (hp : state.locals.lookup (ofString "p") = some (.val (.word p)))
    (hn : state.locals.lookup (ofString "n") = some (.val (.word n)))
    (ho : state.locals.lookup (ofString "out") = some (.val (.word out)))
    (small : n.toNat ≤ 32) (aligned : out.toNat % 8 = 0) (fits : out.toNat + 32 ≤ 33806089496)
    (outside : watched.toNat < out.toNat ∨ out.toNat + 32 ≤ watched.toNat)
    (code : state.code = originalRuntimeCode) (budget : htrBytesVectorShortCost ≤ state.clock)
    (run : evaluateHOLFiniteState state htrBytesVectorShort = (some (.returned value),post)) :
    post.memory watched = state.memory watched := by
  unfold htrBytesVectorShort at run
  obtain ⟨zeroed,zeroRun,tail⟩ := seq_returned_of_nonreturning_first
    (fun v => evaluate_discard_call_no_return state (ofString "memzero") [.var .local (ofString "out"),.const 32] v) run
  have zeroArgs : evalListHOLFinite state (h := fun a => Classical.propDecidable (state.memaddrs a))
      [.var .local (ofString "out"),.const 32] = some [.val (.word out),.val (.word (32#64))] := by
    simp [evalListHOLExact,evalHOLExact,ho]
  obtain ⟨zeroFrame,locals⟩ := memzero_call_normal_memory state zeroed _ out (32#64) watched zeroArgs code aligned fits outside zeroRun
  have meta' := evaluateHOLFiniteState_metadata state
    (.call (some (none,none)) (ofString "memzero") [.var .local (ofString "out"),.const 32])
  have spent := (memzero_const_progBounded (.var .local (ofString "out")) 32 (by decide)) state code
    ((Nat.le_add_right 16 _).trans budget)
  change RunBounded state (.call (some (none,none)) (ofString "memzero") [.var .local (ofString "out"),.const 32]) 16 at spent
  unfold RunBounded at spent
  rw [zeroRun] at meta' spent
  have enough : merkleMemoryCallCost ≤ zeroed.clock := Nat.le_of_add_le_add_right
    ((show merkleMemoryCallCost + 16 ≤ state.clock from by simpa only [htrBytesVectorShortCost,Nat.add_comm] using budget).trans spent.1)
  have args : evalListHOLFinite zeroed (h := fun a => Classical.propDecidable (zeroed.memaddrs a))
      [.var .local (ofString "out"),.var .local (ofString "p"),.var .local (ofString "n")] =
      some [.val (.word out),.val (.word p),.val (.word n)] := by
    simp [evalListHOLExact,evalHOLExact,locals,hp,hn,ho]
  obtain ⟨copied,copyRun,finish⟩ := seq_returned_of_nonreturning_first
    (fun v => evaluate_discard_call_no_return zeroed (ofString "memcpy")
      [.var .local (ofString "out"),.var .local (ofString "p"),.var .local (ofString "n")] v) tail
  have separated := memcpy_interval_separate out n watched aligned (by omega) (by omega)
  have frame := memcpy_call_normal_memory zeroed copied _ out p n watched args (meta'.1.trans code)
    (fun o ho => (separated o ho).1) (fun o ho => (separated o ho).2) (by omega)
    ((merkle_memory_call_cost_le n (by omega)).trans enough) copyRun
  obtain ⟨memory,_,_,_⟩ := return_const_state copied post 0 value finish
  rw [memory]
  exact frame.trans zeroFrame

#print axioms htrBytesVector_short_returned_memory
end InitECandidate.Runtime
