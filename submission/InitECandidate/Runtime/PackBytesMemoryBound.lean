import InitECandidate.Runtime.PackBytesSource
import InitECandidate.Runtime.PackBytesLengths
import InitECandidate.Runtime.MerkleMemoryBound
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

theorem runBounded_packBytes_zero {F : Type} (state : PanSemStateFiniteExact 64 F)
    (buf n : BitVec 64)
    (hb : state.locals.lookup (ofString "buf") = some (.val (.word buf)))
    (hn : state.locals.lookup (ofString "n") = some (.val (.word n)))
    (hc : state.locals.lookup (ofString "count") = some (.val (.word (packBytesCount n))))
    (small : n.toNat ≤ 134217712) (code : state.code = originalRuntimeCode)
    (budget : merkleMemoryCallCost ≤ state.clock) :
    RunBounded state (packBytesAt 3) merkleMemoryCallCost := by
  have lengths := packBytes_lengths n small
  have args : evalListHOLFinite state (h := fun a => Classical.propDecidable (state.memaddrs a)) packBytesZeroArguments =
      some [.val (.word (buf + n)),.val (.word (packBytesCount n * (32#64) - n))] := by
    simp [packBytesZeroArguments,evalListHOLExact,evalHOLExact,hb,hn,hc,wordOpHOL,wordOp,valueIsWord,valueWord,panOpHOL]
  have raw := evaluate_memzero_call_bounded state packBytesZeroArguments (buf + n)
    (packBytesCount n * (32#64) - n) args code (by omega)
    (by have cost := merkle_memory_call_cost_le (packBytesCount n * (32#64) - n) (by omega); omega)
  have bounded : RunBounded state (.call (some (none,none)) (ofString "memzero") packBytesZeroArguments)
      merkleMemoryCallCost := RunBounded.weaken ⟨raw.1,raw.2.1,raw.2.2⟩
        (merkle_memory_call_cost_le _ (by omega))
  rw [source_packBytes_zero]
  have together := RunBounded.seq
    (tail := .return (.rstruct [.var .local (ofString "buf"),.var .local (ofString "count")]))
    (b := 0) bounded (by simpa using budget) (by
    intro next normal nextCode remaining
    exact RunBounded.ofProg (ProgBounded.straight _ (by decide)) (nextCode.trans code) remaining)
  simpa using together

theorem runBounded_packBytes_memory {F : Type} (state : PanSemStateFiniteExact 64 F)
    (buf p n : BitVec 64)
    (hb : state.locals.lookup (ofString "buf") = some (.val (.word buf)))
    (hp : state.locals.lookup (ofString "p") = some (.val (.word p)))
    (hn : state.locals.lookup (ofString "n") = some (.val (.word n)))
    (hc : state.locals.lookup (ofString "count") = some (.val (.word (packBytesCount n))))
    (small : n.toNat ≤ 134217712) (code : state.code = originalRuntimeCode)
    (budget : merkleMemoryCallCost + merkleMemoryCallCost ≤ state.clock) :
    RunBounded state (packBytesAt 2) (merkleMemoryCallCost + merkleMemoryCallCost) := by
  have args : evalListHOLFinite state (h := fun a => Classical.propDecidable (state.memaddrs a)) packBytesCopyArguments =
      some [.val (.word buf),.val (.word p),.val (.word n)] := by
    simp [packBytesCopyArguments,evalListHOLExact,evalHOLExact,hb,hp,hn]
  have raw := evaluate_memcpy_call_bounded state packBytesCopyArguments buf p n args code (by omega)
    (by have cost := merkle_memory_call_cost_le n (by omega); omega)
  have bounded : RunBounded state (.call (some (none,none)) (ofString "memcpy") packBytesCopyArguments)
      merkleMemoryCallCost := RunBounded.weaken ⟨raw.1,raw.2.1,raw.2.2⟩ (merkle_memory_call_cost_le _ (by omega))
  rw [source_packBytes_copy]
  refine RunBounded.seq bounded budget ?_
  intro next run nextCode remaining
  have keep (key : MlS) : next.locals.lookup key = state.locals.lookup key := by
    have frame := evaluate_avoidsLocal_flowing key
      (.call (some (none,none)) (ofString "memcpy") packBytesCopyArguments) rfl state
      (by rw [run]; exact Or.inl rfl)
    simpa only [run] using frame
  exact runBounded_packBytes_zero next buf n ((keep _).trans hb) ((keep _).trans hn) ((keep _).trans hc)
    small (nextCode.trans code) remaining

#print axioms runBounded_packBytes_zero
#print axioms runBounded_packBytes_memory
end InitECandidate.Runtime
