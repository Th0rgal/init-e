import InitECandidate.Runtime.MerkleEmptyBound
import InitECandidate.Runtime.MemcpyCallMemory
import InitECandidate.Runtime.MemcpyIntervalFrame
import InitECandidate.Runtime.PanDiscardReturnMemory
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

theorem merkleEmpty_branch_returned_memory {F : Type} (state post : PanSemStateFiniteExact 64 F)
    (zeroHashes target out watched : BitVec 64) (value : ValueHOL 64)
    (atZero : state.globals.lookup (ofString "zero_hashes") = some (.val (.word zeroHashes)))
    (atTarget : state.locals.lookup (ofString "target") = some (.val (.word target)))
    (atOut : state.locals.lookup (ofString "out") = some (.val (.word out)))
    (aligned : out.toNat % 8 = 0) (fits : out.toNat + 32 ≤ 33806089496)
    (outside : watched.toNat < out.toNat ∨ out.toNat + 32 ≤ watched.toNat)
    (code : state.code = originalRuntimeCode) (budget : 16 ≤ state.clock)
    (run : evaluateHOLFiniteState state merkleEmptyBranch = (some (.returned value),post)) :
    post.memory watched = state.memory watched := by
  rw [source_merkleEmpty_branch] at run
  obtain ⟨middle,normal,memory⟩ := evaluate_discard_then_return_memory state post (ofString "memcpy")
    _ (.return (.const 0)) value rfl run
  have separate := memcpy_interval_separate out (32#64) watched aligned fits outside
  have frame := memcpy_call_normal_memory state middle _ out (zeroHashes + target * (32#64)) (32#64) watched
    (by simp [evalListHOLExact,evalHOLExact,atOut,atZero,atTarget,wordOpHOL,wordOp,valueIsWord,valueWord,panOpHOL]) code
    (fun offset inside => (separate offset inside).1) (fun offset inside => (separate offset inside).2)
    (by decide) budget normal
  exact (congrFun memory watched).trans frame

#print axioms merkleEmpty_branch_returned_memory
end InitECandidate.Runtime
