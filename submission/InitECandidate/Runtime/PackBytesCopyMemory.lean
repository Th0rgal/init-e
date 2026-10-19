import InitECandidate.Runtime.PackBytesZeroMemory
import InitECandidate.Runtime.PackBytesMemoryBound
import InitECandidate.Runtime.MemcpyCallMemory
import InitECandidate.Runtime.MarkedHeapReturn
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

theorem packBytes_memory_returned_frame {F : Type} (state post : PanSemStateFiniteExact 64 F)
    (buf p n watched : BitVec 64) (value : ValueHOL 64)
    (hb : state.locals.lookup (ofString "buf") = some (.val (.word buf)))
    (hp : state.locals.lookup (ofString "p") = some (.val (.word p)))
    (hn : state.locals.lookup (ofString "n") = some (.val (.word n)))
    (hc : state.locals.lookup (ofString "count") = some (.val (.word (packBytesCount n))))
    (small : n.toNat ≤ 134217712) (aligned : buf.toNat % 8 = 0)
    (fits : buf.toNat + (packBytesCount n * (32#64)).toNat ≤ 33806089496)
    (outside : watched.toNat < buf.toNat ∨ buf.toNat + (packBytesCount n * (32#64)).toNat ≤ watched.toNat)
    (code : state.code = originalRuntimeCode)
    (budget : merkleMemoryCallCost ≤ state.clock)
    (run : evaluateHOLFiniteState state (packBytesAt 2) = (some (.returned value),post)) :
    post.memory watched = state.memory watched := by
  have lengths := packBytes_lengths n small
  have covers : n.toNat ≤ (packBytesCount n * (32#64)).toNat := by rw [lengths.2.2.1]; exact lengths.2.2.2.1
  have copyFits : buf.toNat + n.toNat ≤ 33806089496 := by omega
  have copyOutside : watched.toNat < buf.toNat ∨ buf.toNat + n.toNat ≤ watched.toNat := by
    rcases outside with before | after
    · exact Or.inl before
    · exact Or.inr (by omega)
  have separate := memcpy_interval_separate buf n watched aligned copyFits copyOutside
  rw [source_packBytes_copy] at run
  obtain ⟨middle,normal,tail⟩ := seq_returned_of_nonreturning_first
    (fun v => evaluate_discard_call_no_return state (ofString "memcpy") packBytesCopyArguments v) run
  have frame := memcpy_call_normal_memory state middle packBytesCopyArguments buf p n watched
    (by simp [packBytesCopyArguments,evalListHOLExact,evalHOLExact,hb,hp,hn]) code
    (fun offset inside => (separate offset inside).1) (fun offset inside => (separate offset inside).2)
    (by omega) (by have cost := merkle_memory_call_cost_le n (by omega); omega) normal
  have keep (key : MlS) : middle.locals.lookup key = state.locals.lookup key := by
    have locals := evaluate_avoidsLocal_flowing key (.call (some (none,none)) (ofString "memcpy") packBytesCopyArguments)
      rfl state (by rw [normal]; exact Or.inl rfl)
    simpa only [normal] using locals
  have meta' := evaluateHOLFiniteState_metadata state (.call (some (none,none)) (ofString "memcpy") packBytesCopyArguments)
  rw [normal] at meta'
  have suffix := packBytes_zero_returned_memory middle post buf n watched value
    ((keep _).trans hb) ((keep _).trans hn) ((keep _).trans hc) small aligned fits outside (meta'.1.trans code) tail
  exact suffix.trans frame

#print axioms packBytes_memory_returned_frame
end InitECandidate.Runtime
