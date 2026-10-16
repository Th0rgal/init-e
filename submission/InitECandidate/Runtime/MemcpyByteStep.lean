import InitECandidate.Runtime.MemcpyWordStep
import InitECandidate.Runtime.SourceByteStore
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

def memcpyByte1Body : ProgHOL 64 :=
  .seq (.storeByte (memcpyAddress (ofString "dst")) (.loadByte (memcpyAddress (ofString "src")))) (memzeroAdvance 1)

def memcpyByte1Loop : ProgHOL 64 :=
  match memcpyAfterAligned with | .seq _ (.seq loop _) => loop | _ => .skip

theorem source_memcpy_byte1_loop : memcpyByte1Loop =
    .while (.cmp .lower (.var .local (ofString "i")) (.var .local (ofString "n"))) memcpyByte1Body := by rfl

/-- Actual final byte-copy iteration loads before storing, advances one byte
and consumes no source clock. Both endian modes use the original byte codec. -/
theorem evaluate_memcpy_byte1_body {F : Type} (state : PanSemStateFiniteExact 64 F)
    (destination source index cell : BitVec 64) (byte : UInt8)
    (dstLocal : state.locals.lookup (ofString "dst") = some (.val (.word destination)))
    (srcLocal : state.locals.lookup (ofString "src") = some (.val (.word source)))
    (indexLocal : state.locals.lookup (ofString "i") = some (.val (.word index)))
    (loaded : @panMemLoadByteHOL 64 _ state.memory state.memaddrs
      (fun address => Classical.propDecidable (state.memaddrs address)) state.be (source + index) = some byte)
    (domain : state.memaddrs (panByteAlignHOL (destination + index)))
    (memory : state.memory (panByteAlignHOL (destination + index)) = .word cell) :
    evaluateHOLFiniteState state memcpyByte1Body =
      (none,setVarHOLFinite (ofString "i") (.val (.word (index + 1)))
        (sourceWriteByte state (destination + index) (BitVec.ofNat 64 byte.toNat) cell)) := by
  have sourceAddress := eval_memcpyAddress state (ofString "src") source index srcLocal indexLocal
  have destinationAddress := eval_memcpyAddress state (ofString "dst") destination index dstLocal indexLocal
  have value : @evalHOLExact 64 F _ state.toExact
      (fun address => Classical.propDecidable (state.memaddrs address))
      (.loadByte (memcpyAddress (ofString "src"))) = some (.val (.word (BitVec.ofNat 64 byte.toNat))) := by
    rw [evalHOLExact,sourceAddress]
    simp only [loaded,Option.map_some]
  have store := evaluate_source_storeByte state _ _ (destination + index) (BitVec.ofNat 64 byte.toNat) cell
    destinationAddress value domain memory
  have advance := evaluate_memzero_advance
    (sourceWriteByte state (destination + index) (BitVec.ofNat 64 byte.toNat) cell) index 1 indexLocal
  unfold memcpyByte1Body
  rw [evaluateHOLFiniteState_seq_line780,store]
  exact advance

/-- Readable source and destination aligned cells suffice for a byte step;
contents may be arbitrary and the source may overlap the destination. -/
theorem evaluate_memcpy_byte1_step {F : Type} (state : PanSemStateFiniteExact 64 F)
    (destination source index : BitVec 64)
    (dstLocal : state.locals.lookup (ofString "dst") = some (.val (.word destination)))
    (srcLocal : state.locals.lookup (ofString "src") = some (.val (.word source)))
    (indexLocal : state.locals.lookup (ofString "i") = some (.val (.word index)))
    (destinationDomain : state.memaddrs (panByteAlignHOL (destination + index)))
    (sourceDomain : state.memaddrs (panByteAlignHOL (source + index))) :
    ∃ post, evaluateHOLFiniteState state memcpyByte1Body = (none,post) ∧ post.clock = state.clock ∧
      post.locals.lookup (ofString "i") = some (.val (.word (index + 1))) ∧
      post.globals = state.globals ∧ post.code = state.code ∧ post.memaddrs = state.memaddrs ∧ post.be = state.be ∧
      (∀ name, name ≠ ofString "i" → post.locals.lookup name = state.locals.lookup name) ∧
      ∀ capacity used : BitVec 64,
        (∀ slot : BitVec 64, slot.toNat < capacity.toNat →
          panByteAlignHOL (used + slot) ≠ panByteAlignHOL (destination + index)) →
        hashOccupiedCount capacity (hashOccupancyRead post used) = hashOccupiedCount capacity (hashOccupancyRead state used) := by
  obtain ⟨src,srcMemory⟩ : ∃ value : BitVec 64, state.memory (panByteAlignHOL (source + index)) = .word value := by
    cases state.memory (panByteAlignHOL (source + index)) with | word value => exact ⟨value,rfl⟩
  obtain ⟨dst,dstMemory⟩ : ∃ value : BitVec 64, state.memory (panByteAlignHOL (destination + index)) = .word value := by
    cases state.memory (panByteAlignHOL (destination + index)) with | word value => exact ⟨value,rfl⟩
  let byte := panGetByteHOL (source + index) src state.be
  have loaded : @panMemLoadByteHOL 64 _ state.memory state.memaddrs
      (fun address => Classical.propDecidable (state.memaddrs address)) state.be (source + index) = some byte := by
    simp [panMemLoadByteHOL,srcMemory,sourceDomain,byte]
  have run := evaluate_memcpy_byte1_body state destination source index dst byte dstLocal srcLocal indexLocal
    loaded destinationDomain dstMemory
  refine ⟨_,run,rfl,?_,rfl,rfl,rfl,rfl,?_,?_⟩
  · simp [setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]
  · intro name different
    simp [setVarHOLFinite,sourceWriteByte,HolFiniteMapExact.lookup_update,FUPDATE,Ne.symm different]
  · intro capacity used separate
    apply hashOccupiedCount_congr
    intro slot inside
    exact sourceWriteByte_load_other_word state (destination + index) (BitVec.ofNat 64 byte.toNat) dst (used + slot)
      (separate slot inside)

#print axioms evaluate_memcpy_byte1_step
#print axioms source_memcpy_byte1_loop
#print axioms evaluate_memcpy_byte1_body
end InitECandidate.Runtime
