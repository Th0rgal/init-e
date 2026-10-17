import InitECandidate.Runtime.DecodeStepExtensionRecord
import InitECandidate.Runtime.ScratchAllocationGeometry
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- The parser record contract follows from the scratch arena and the aligned
heap-path interval, without a supplied per-byte separation certificate. -/
theorem evaluate_decodeStep_extension_record_arena {F : Type} (state : PanSemStateFiniteExact 64 F)
    (scratch frame arr pointer length nibs count leaf : BitVec 64)
    (arrLocal : state.locals.lookup (ofString "arr") = some (.val (.word arr)))
    (pointerLocal : state.locals.lookup (ofString "p") = some (.val (.word pointer)))
    (lengthLocal : state.locals.lookup (ofString "n") = some (.val (.word length)))
    (pathLocal : state.locals.lookup (ofString "cn") = some
      (.rStruct [.val (.word nibs),.val (.word count),.val (.word leaf)]))
    (valid : TrieNibbleRange state nibs count)
    (code : state.code = originalRuntimeCode) (ticks : 1 ≤ state.clock)
    (scratchGlobal : state.globals.lookup (ofString "scratch_ptr") = some (.val (.word scratch)))
    (frameGlobal : state.globals.lookup (ofString "frame_mem_ptr") = some (.val (.word frame)))
    (request : (88 : BitVec 64) ≤ scratch - frame)
    (within : frame ≤ scratchAllocationEnd scratch 88)
    (fits : 88 ≤ scratch.toNat)
    (below : scratch.toNat ≤ nibs.toNat)
    (aligned : nibs.toNat % 8 = 0)
    (bounded : nibs.toNat + count.toNat ≤ 2^64)
    (arena : ∀ address : BitVec 64, frame.toNat ≤ address.toNat → address.toNat < scratch.toNat → state.memaddrs address) :
    ∃ post, evaluateHOLFiniteState state decodeStepExtensionRecord =
        (some (.returned (.rStruct [.val (.word (1 : BitVec 64)),.val (.word (scratchAllocationEnd scratch 88))])),post) ∧
      post.clock = state.clock - 1 ∧ TrieNibbleRange post nibs count ∧
      post.memory (scratchAllocationEnd scratch 88 + 64) = .word nibs ∧
      post.memory (scratchAllocationEnd scratch 88 + 72) = .word count := by
  have domain : ∀ offset ∈ ([8,24,48,56,64,72] : List Nat),
      state.memaddrs (scratchAllocationEnd scratch 88 + BitVec.ofNat 64 offset) := by
    intro offset member
    have small : offset < 88 := by simp at member; omega
    have fieldNat := scratchRecord_field_nat scratch offset fits small
    apply arena _ _ fieldNat.2
    have startBound := BitVec.le_def.mp within
    rw [fieldNat.1]
    omega
  have separate := scratchRecord_path_separate scratch nibs count fits below aligned bounded
  exact evaluate_decodeStep_extension_record state scratch frame arr pointer length nibs count leaf
    arrLocal pointerLocal lengthLocal pathLocal valid code ticks scratchGlobal frameGlobal request within domain
    (by intro offset inside field member; apply separate offset inside field; simp at member; omega)

#print axioms evaluate_decodeStep_extension_record_arena
end InitECandidate.Runtime
