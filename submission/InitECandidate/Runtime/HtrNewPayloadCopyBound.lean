import InitECandidate.Runtime.HtrNewPayloadFinalBound
import InitECandidate.Runtime.MemcpyCallMemory
import InitECandidate.Runtime.MemcpyIntervalFrame
import InitECandidate.Runtime.KeccakGlobalsFrame
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
set_option maxRecDepth 100000

def htrNewPayloadCopyCost : Nat := 16 + htrNewPayloadRequestsCost

/-- The actual parent-root copy preserves the stateless header and decoded
request table before the bounded requests/final-Merkle suffix. -/
theorem runBounded_htrNewPayload_copy_suffix {F : Type} (state : PanSemStateFiniteExact 64 F)
    (sha accelerator zeroHashes chunk record heap si chunks out parentRoot : BitVec 64)
    (workspace : HtrRequestsWorkspace state sha accelerator zeroHashes chunk record heap)
    (decoded : HtrRequestsDecoded state record)
    (atSi : state.locals.lookup (ofString "si") = some (.val (.word si)))
    (atChunks : state.locals.lookup (ofString "ch") = some (.val (.word chunks)))
    (atOut : state.locals.lookup (ofString "out") = some (.val (.word out)))
    (requestDomain : state.memaddrs (si + (32#64))) (requestCell : state.memory (si + (32#64)) = .word record)
    (parentDomain : state.memaddrs (si + (24#64))) (parentCell : state.memory (si + (24#64)) = .word parentRoot)
    (chunksAligned : chunks.toNat % 8 = 0) (chunksFits : chunks.toNat + 128 ≤ 33806089496)
    (siBefore : si.toNat + 32 < chunks.toNat) (recordBefore : record.toNat + 72 < chunks.toNat)
    (budget : htrNewPayloadCopyCost ≤ state.clock) :
    RunBounded state (htrNewPayloadAt 4) htrNewPayloadCopyCost := by
  have args : evalListHOLFinite state (h := fun a => Classical.propDecidable (state.memaddrs a)) htrNewPayloadCopyArguments =
      some [.val (.word (chunks + (64#64))),.val (.word parentRoot),.val (.word (32#64))] := by
    simp [htrNewPayloadCopyArguments,htrNewPayloadRead,htrNewPayloadAddress,evalListHOLExact,evalHOLExact,atSi,atChunks,
      wordOpHOL,wordOp,valueIsWord,valueWord,isWfShapeExactHOL,memLoadHOLExact,parentDomain,parentCell]
  have natural : (chunks + (64#64)).toNat = chunks.toNat + 64 := word_add_toNat chunks 64 (by omega)
  have aligned : (chunks + (64#64)).toNat % 8 = 0 := by rw [natural,Nat.add_mod,chunksAligned]
  have enough : 16 ≤ state.clock := (Nat.le_add_right 16 htrNewPayloadRequestsCost).trans budget
  have first : RunBounded state (.call (some (none,none)) (ofString "memcpy") htrNewPayloadCopyArguments) 16 :=
    evaluate_memcpy_call_bounded state htrNewPayloadCopyArguments (chunks + (64#64)) parentRoot (32#64)
      args workspace.code (by decide) (by change 16 ≤ state.clock; exact enough)
  rw [source_htrNewPayload_copy]
  exact RunBounded.seq first budget (by
    intro next normal nextCode remaining
    have metadata := evaluateHOLFiniteState_metadata state (.call (some (none,none)) (ofString "memcpy") htrNewPayloadCopyArguments)
    have globals := memcpy_call_globals_frame htrNewPayloadCopyArguments state workspace.code
    rw [normal] at metadata globals
    have frame (watched : BitVec 64) (before : watched.toNat < chunks.toNat) : next.memory watched = state.memory watched := by
      have separation := memcpy_interval_separate (chunks + (64#64)) (32#64) watched aligned
        (by rw [natural]; change _ + 32 ≤ _; omega) (Or.inl (by rw [natural]; omega))
      exact memcpy_call_normal_memory state next htrNewPayloadCopyArguments (chunks + (64#64)) parentRoot (32#64) watched args workspace.code
        (fun offset inside => (separation offset inside).1) (fun offset inside => (separation offset inside).2)
        (by decide) (by change 16 ≤ state.clock; exact enough) normal
    have decodedKept : HtrRequestsDecoded next record := by
      intro index inside
      obtain ⟨pointer,count,entry,small⟩ := decoded index inside
      refine ⟨pointer,count,?_,small⟩
      apply entry.after_record_frame state next record index pointer count inside (by omega) metadata.2.1
      intro watched lo hi
      exact frame watched (by omega)
    have keep (key : MlS) : next.locals.lookup key = state.locals.lookup key := by
      have kept := evaluate_avoidsLocal_flowing key (.call (some (none,none)) (ofString "memcpy") htrNewPayloadCopyArguments)
        rfl state (by rw [normal]; exact Or.inl rfl)
      rw [normal] at kept
      exact kept
    have headerNat : (si + (32#64)).toNat = si.toNat + 32 := word_add_toNat si 32 (by omega)
    exact runBounded_htrNewPayload_requests_suffix next sha accelerator zeroHashes chunk record heap si chunks out
      (workspace.transfer globals nextCode) decodedKept ((keep _).trans atSi) ((keep _).trans atChunks) ((keep _).trans atOut)
      (by rw [metadata.2.1]; exact requestDomain) ((frame _ (by rw [headerNat]; omega)).trans requestCell) remaining)

#print axioms runBounded_htrNewPayload_copy_suffix
end InitECandidate.Runtime
