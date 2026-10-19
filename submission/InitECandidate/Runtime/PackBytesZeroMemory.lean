import InitECandidate.Runtime.PackBytesSource
import InitECandidate.Runtime.PackBytesLengths
import InitECandidate.Runtime.MemzeroSeparatedMemory
import InitECandidate.Runtime.SubintervalMemorySeparation
import InitECandidate.Runtime.PanDiscardReturnMemory
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- The actual pack-bytes padding call may be unaligned. Its aligned byte
writes nevertheless stay inside the original aligned allocation. -/
theorem packBytes_zero_returned_memory {F : Type} (state post : PanSemStateFiniteExact 64 F)
    (buf n watched : BitVec 64) (value : ValueHOL 64)
    (hb : state.locals.lookup (ofString "buf") = some (.val (.word buf)))
    (hn : state.locals.lookup (ofString "n") = some (.val (.word n)))
    (hc : state.locals.lookup (ofString "count") = some (.val (.word (packBytesCount n))))
    (small : n.toNat ≤ 134217712) (aligned : buf.toNat % 8 = 0)
    (fits : buf.toNat + (packBytesCount n * (32#64)).toNat ≤ 33806089496)
    (outside : watched.toNat < buf.toNat ∨ buf.toNat + (packBytesCount n * (32#64)).toNat ≤ watched.toNat)
    (code : state.code = originalRuntimeCode)
    (run : evaluateHOLFiniteState state (packBytesAt 3) = (some (.returned value),post)) :
    post.memory watched = state.memory watched := by
  have lengths := packBytes_lengths n small
  have covers : n.toNat ≤ (packBytesCount n * (32#64)).toNat := by rw [lengths.2.2.1]; exact lengths.2.2.2.1
  have paddingNat : (packBytesCount n * (32#64) - n).toNat =
      (packBytesCount n * (32#64)).toNat - n.toNat :=
    BitVec.toNat_sub_of_le (BitVec.le_def.mpr covers)
  have geometry := aligned_subinterval_memory_separate buf (packBytesCount n * (32#64)) n
    (packBytesCount n * (32#64) - n) watched aligned fits (by rw [paddingNat]; omega) outside
  rw [source_packBytes_zero] at run
  obtain ⟨middle,normal,memory⟩ := evaluate_discard_then_return_memory state post (ofString "memzero")
    packBytesZeroArguments (.return (.rstruct [.var .local (ofString "buf"),.var .local (ofString "count")]))
    value rfl run
  have frame := memzero_call_normal_separated_memory state middle packBytesZeroArguments (buf + n)
    (packBytesCount n * (32#64) - n) watched
    (by simp [packBytesZeroArguments,evalListHOLExact,evalHOLExact,hb,hn,hc,
      wordOpHOL,wordOp,valueIsWord,valueWord,panOpHOL]) code geometry.1 geometry.2 normal
  exact (congrFun memory watched).trans frame.1

#print axioms packBytes_zero_returned_memory
end InitECandidate.Runtime
