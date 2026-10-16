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

#print axioms source_memcpy_byte1_loop
#print axioms evaluate_memcpy_byte1_body
end InitECandidate.Runtime
