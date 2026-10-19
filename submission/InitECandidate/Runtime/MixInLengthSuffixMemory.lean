import InitECandidate.Runtime.MixInLengthSource
import InitECandidate.Runtime.Sha256PairMemory
import InitECandidate.Runtime.StoreLE64Memory
import InitECandidate.Runtime.AllocationSeparation
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

theorem mixLength_hash_returned_memory {F : Type} (state post : PanSemStateFiniteExact 64 F)
    (pointer accelerator chunk out root length watched : BitVec 64) (value : ValueHOL 64)
    (atPointer : state.globals.lookup (ofString "sha_st") = some (.val (.word pointer)))
    (atAccel : state.globals.lookup (ofString "sha_accel") = some (.val (.word accelerator)))
    (atChunk : state.globals.lookup (ofString "ssz_len_chunk") = some (.val (.word chunk)))
    (atOut : state.locals.lookup (ofString "out") = some (.val (.word out)))
    (atRoot : state.locals.lookup (ofString "root") = some (.val (.word root)))
    (atLength : state.locals.lookup (ofString "len") = some (.val (.word length)))
    (accelAligned : accelerator.toNat % 8 = 0) (chunkAligned : chunk.toNat % 8 = 0)
    (outAligned : out.toNat % 8 = 0)
    (accelFits : accelerator.toNat + 96 ≤ 33806089496) (pointerFits : pointer.toNat + 64 ≤ 33806089496)
    (chunkFits : chunk.toNat + 32 ≤ 33806089496) (outFits : out.toNat + 32 ≤ 33806089496)
    (accelOutside : watched.toNat < accelerator.toNat ∨ accelerator.toNat + 96 ≤ watched.toNat)
    (pointerOutside : watched.toNat < pointer.toNat ∨ pointer.toNat + 64 ≤ watched.toNat)
    (chunkOutside : watched.toNat < chunk.toNat ∨ chunk.toNat + 32 ≤ watched.toNat)
    (outOutside : watched.toNat < out.toNat ∨ out.toNat + 32 ≤ watched.toNat)
    (code : state.code = originalRuntimeCode) (budget : 119 ≤ state.clock)
    (run : evaluateHOLFiniteState state (mixLengthAt 2) = (some (.returned value),post)) :
    post.memory watched = state.memory watched := by
  rw [source_mixLength_hash] at run
  obtain ⟨middle,normal,memory⟩ := evaluate_discard_then_return_memory state post (ofString "sha256_pair")
    mixLengthHashArguments (.return (.const 0)) value rfl run
  have frame := shaPair_call_normal_memory state middle mixLengthHashArguments pointer accelerator out root chunk watched
    (by simp [mixLengthHashArguments,evalListHOLExact,evalHOLExact,atRoot,atChunk,atOut]) atPointer atAccel
    accelAligned outAligned accelFits pointerFits outFits accelOutside pointerOutside outOutside code budget normal
  exact (congrFun memory watched).trans frame

theorem mixLength_store_returned_memory {F : Type} (state post : PanSemStateFiniteExact 64 F)
    (pointer accelerator chunk out root length watched : BitVec 64) (value : ValueHOL 64)
    (atPointer : state.globals.lookup (ofString "sha_st") = some (.val (.word pointer)))
    (atAccel : state.globals.lookup (ofString "sha_accel") = some (.val (.word accelerator)))
    (atChunk : state.globals.lookup (ofString "ssz_len_chunk") = some (.val (.word chunk)))
    (atOut : state.locals.lookup (ofString "out") = some (.val (.word out)))
    (atRoot : state.locals.lookup (ofString "root") = some (.val (.word root)))
    (atLength : state.locals.lookup (ofString "len") = some (.val (.word length)))
    (accelAligned : accelerator.toNat % 8 = 0) (chunkAligned : chunk.toNat % 8 = 0)
    (outAligned : out.toNat % 8 = 0)
    (accelFits : accelerator.toNat + 96 ≤ 33806089496) (pointerFits : pointer.toNat + 64 ≤ 33806089496)
    (chunkFits : chunk.toNat + 32 ≤ 33806089496) (outFits : out.toNat + 32 ≤ 33806089496)
    (accelOutside : watched.toNat < accelerator.toNat ∨ accelerator.toNat + 96 ≤ watched.toNat)
    (pointerOutside : watched.toNat < pointer.toNat ∨ pointer.toNat + 64 ≤ watched.toNat)
    (chunkOutside : watched.toNat < chunk.toNat ∨ chunk.toNat + 32 ≤ watched.toNat)
    (outOutside : watched.toNat < out.toNat ∨ out.toNat + 32 ≤ watched.toNat)
    (code : state.code = originalRuntimeCode) (budget : 122 ≤ state.clock)
    (run : evaluateHOLFiniteState state (mixLengthAt 1) = (some (.returned value),post)) :
    post.memory watched = state.memory watched := by
  let arguments : List (ExpHOL 64) := [.var .global (ofString "ssz_len_chunk"),.var .local (ofString "len")]
  have separate : ∀ offset : Nat, offset < 8 → watched ≠ panByteAlignHOL (chunk + BitVec.ofNat 64 offset) := by
    intro offset inside same
    have offsetNat : (BitVec.ofNat 64 offset).toNat = offset := Nat.mod_eq_of_lt (by omega)
    have interval := hashOccupancy_aligned_interval chunk (32#64) (BitVec.ofNat 64 offset) chunkAligned
      (by change chunk.toNat + 32 ≤ 2 ^ 64; omega) (by change _ < 32; rw [offsetNat]; omega)
    have natural := congrArg BitVec.toNat same
    change chunk.toNat ≤ _ ∧ _ < chunk.toNat + 32 at interval
    rcases chunkOutside with before | after <;> omega
  rw [source_mixLength_store] at run
  obtain ⟨middle,normal,tail⟩ := seq_returned_of_nonreturning_first
    (fun v => evaluate_discard_call_no_return state (ofString "st_le64") arguments v) run
  have frame := storeLE64_call_normal_memory state middle arguments chunk length watched
    (by simp [arguments,evalListHOLExact,evalHOLExact,atChunk,atLength]) code separate normal
  have globals := storeLE64_call_globals_frame arguments state code
  have meta' := evaluateHOLFiniteState_metadata state (.call (some (none,none)) (ofString "st_le64") arguments)
  have clocks := vmBound_st_le64.call_bounded state none arguments code (by omega)
  rw [normal] at globals meta' clocks
  have keep (key : MlS) : middle.locals.lookup key = state.locals.lookup key := by
    have locals := evaluate_avoidsLocal_flowing key (.call (some (none,none)) (ofString "st_le64") arguments)
      rfl state (by rw [normal]; exact Or.inl rfl)
    simpa only [normal] using locals
  have suffix := mixLength_hash_returned_memory middle post pointer accelerator chunk out root length watched value
    (by rw [globals]; exact atPointer) (by rw [globals]; exact atAccel) (by rw [globals]; exact atChunk)
    ((keep _).trans atOut) ((keep _).trans atRoot) ((keep _).trans atLength)
    accelAligned chunkAligned outAligned accelFits pointerFits chunkFits outFits
    accelOutside pointerOutside chunkOutside outOutside (meta'.1.trans code) (by dsimp only at clocks; omega) tail
  exact suffix.trans frame

#print axioms mixLength_hash_returned_memory
#print axioms mixLength_store_returned_memory
end InitECandidate.Runtime
