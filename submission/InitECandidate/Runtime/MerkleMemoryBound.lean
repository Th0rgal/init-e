import InitECandidate.Runtime.MerkleMemorySource
import InitECandidate.Runtime.MerkleChunkLengths
import InitECandidate.Runtime.MerkleSuffixBound
import InitECandidate.Runtime.MemcpyCallBound
import InitECandidate.Runtime.MemzeroCallBound
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

def merkleMemoryCallCost : Nat := 4294967296 / 32 + 4294967296 / 8 + 11

theorem merkle_memory_call_cost_le (bytes : BitVec 64) (bound : bytes.toNat ≤ 4294967296) :
    bytes.toNat / 32 + bytes.toNat / 8 + 11 ≤ merkleMemoryCallCost := by
  unfold merkleMemoryCallCost
  omega

def merkleZeroSuffixCost : Nat := merkleMemoryCallCost + merkleSuffixCost
def merkleMemorySuffixCost : Nat := merkleMemoryCallCost + merkleZeroSuffixCost

/-- The real zeroing call and remaining Merkle computation are bounded using
the nonwrapping chunk lengths, with all memory errors and exits included. -/
theorem runBounded_merkleZeroSuffix {F : Type} (state : PanSemStateFiniteExact 64 F)
    (buf n size dn target : BitVec 64)
    (buffer : state.locals.lookup (ofString "buf") = some (.val (.word buf)))
    (count : state.locals.lookup (ofString "n") = some (.val (.word n)))
    (sizeLocal : state.locals.lookup (ofString "size") = some (.val (.word size)))
    (depth : state.locals.lookup (ofString "dn") = some (.val (.word dn)))
    (limit : state.locals.lookup (ofString "target") = some (.val (.word target)))
    (lengths : MerkleChunkLengths n size) (depthBound : dn.toNat ≤ 27) (targetBound : target.toNat ≤ 63)
    (code : state.code = originalRuntimeCode) (budget : merkleZeroSuffixCost ≤ state.clock) :
    RunBounded state (merkleizeAt 8) merkleZeroSuffixCost := by
  have sizeBound := lengths.2.1
  have zeroBound := lengths.2.2.2.2.2.2.2.1
  have args : evalListHOLFinite state (h := fun a => Classical.propDecidable (state.memaddrs a))
      merkleZeroArguments = some [.val (.word (buf + n * (32#64))),.val (.word ((size - n) * (32#64)))] := by
    simp [merkleZeroArguments,evalListHOLFinite_eq_toExact,evalListHOLExact,evalHOLExact,buffer,count,sizeLocal,
      wordOpHOL,wordOp,valueIsWord,valueWord,panOpHOL]
  have cost := merkle_memory_call_cost_le ((size - n) * (32#64)) zeroBound
  have raw := evaluate_memzero_call_bounded state merkleZeroArguments (buf + n * (32#64)) ((size - n) * (32#64))
    args code (by omega) (by unfold merkleZeroSuffixCost at budget; omega)
  have firstBound : RunBounded state (.call (some (none,none)) (ofString "memzero") merkleZeroArguments)
      merkleMemoryCallCost := RunBounded.weaken ⟨raw.1,raw.2.1,raw.2.2⟩ cost
  rw [source_merkleZero]
  refine RunBounded.seq firstBound budget ?_
  intro next run nextCode remaining
  have keep (key : MlS) : next.locals.lookup key = state.locals.lookup key := by
    have frame := evaluate_avoidsLocal_flowing key
      (.call (some (none,none)) (ofString "memzero") merkleZeroArguments) (by rfl) state
      (by rw [run]; exact Or.inl rfl)
    simpa only [run] using frame
  exact runBounded_merkleCurSuffix next size dn target ((keep _).trans sizeLocal)
    ((keep _).trans depth) ((keep _).trans limit) sizeBound depthBound targetBound (nextCode.trans code) remaining

/-- The actual data copy and zero-fill prefix compose with the checked level,
padding and return suffix. No array readability premise is needed for runtime. -/
theorem runBounded_merkleMemorySuffix {F : Type} (state : PanSemStateFiniteExact 64 F)
    (buf pointer n size dn target : BitVec 64)
    (buffer : state.locals.lookup (ofString "buf") = some (.val (.word buf)))
    (input : state.locals.lookup (ofString "p") = some (.val (.word pointer)))
    (count : state.locals.lookup (ofString "n") = some (.val (.word n)))
    (sizeLocal : state.locals.lookup (ofString "size") = some (.val (.word size)))
    (depth : state.locals.lookup (ofString "dn") = some (.val (.word dn)))
    (limit : state.locals.lookup (ofString "target") = some (.val (.word target)))
    (lengths : MerkleChunkLengths n size) (depthBound : dn.toNat ≤ 27) (targetBound : target.toNat ≤ 63)
    (code : state.code = originalRuntimeCode) (budget : merkleMemorySuffixCost ≤ state.clock) :
    RunBounded state (merkleizeAt 7) merkleMemorySuffixCost := by
  have copyBound := lengths.2.2.2.2.2.2.1
  have args : evalListHOLFinite state (h := fun a => Classical.propDecidable (state.memaddrs a))
      merkleCopyArguments = some [.val (.word buf),.val (.word pointer),.val (.word (n * (32#64)))] := by
    simp [merkleCopyArguments,evalListHOLFinite_eq_toExact,evalListHOLExact,evalHOLExact,buffer,input,count,
      wordOpHOL,wordOp,valueIsWord,valueWord,panOpHOL]
  have cost := merkle_memory_call_cost_le (n * (32#64)) copyBound
  have raw := evaluate_memcpy_call_bounded state merkleCopyArguments buf pointer (n * (32#64)) args code
    (by omega) (by unfold merkleMemorySuffixCost at budget; omega)
  have firstBound : RunBounded state (.call (some (none,none)) (ofString "memcpy") merkleCopyArguments)
      merkleMemoryCallCost := RunBounded.weaken ⟨raw.1,raw.2.1,raw.2.2⟩ cost
  rw [source_merkleCopy]
  refine RunBounded.seq firstBound budget ?_
  intro next run nextCode remaining
  have keep (key : MlS) : next.locals.lookup key = state.locals.lookup key := by
    have frame := evaluate_avoidsLocal_flowing key
      (.call (some (none,none)) (ofString "memcpy") merkleCopyArguments) (by rfl) state
      (by rw [run]; exact Or.inl rfl)
    simpa only [run] using frame
  exact runBounded_merkleZeroSuffix next buf n size dn target ((keep _).trans buffer) ((keep _).trans count)
    ((keep _).trans sizeLocal) ((keep _).trans depth) ((keep _).trans limit) lengths depthBound targetBound
    (nextCode.trans code) remaining

#print axioms merkle_memory_call_cost_le
#print axioms runBounded_merkleZeroSuffix
#print axioms runBounded_merkleMemorySuffix
end InitECandidate.Runtime
