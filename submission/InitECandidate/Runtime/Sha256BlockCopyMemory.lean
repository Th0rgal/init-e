import InitECandidate.Runtime.Sha256BlockSource
import InitECandidate.Runtime.MemcpyCallMemory
import InitECandidate.Runtime.MemcpyIntervalFrame
import InitECandidate.Runtime.KeccakGlobalsFrame
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

def shaBlockCopyCheck : ProgHOL 64 :=
  .ite (.cmp .notEqual (.var .local (ofString "blk")) (.op .add [.var .global (ofString "sha_accel"),.const 32]))
    (.call (some (none,none)) (ofString "memcpy")
      [.op .add [.var .global (ofString "sha_accel"),.const 32],.var .local (ofString "blk"),.const 64]) .skip

theorem source_shaBlock_copy_check : shaBlockAt 0 = .seq shaBlockCopyCheck (shaBlockAt 1) := by rfl

theorem shaBlockCopy_globals : OriginalGlobalsFrame shaBlockCopyCheck :=
  originalGlobalsFrame_conditional _ _ _ (memcpy_call_globals_frame _) (originalGlobalsFrame_leaf _ (by intro watched; rfl))

theorem shaBlockCopy_normal_memory {F : Type} (state post : PanSemStateFiniteExact 64 F)
    (block accelerator watched : BitVec 64)
    (atBlock : state.locals.lookup (ofString "blk") = some (.val (.word block)))
    (atAccel : state.globals.lookup (ofString "sha_accel") = some (.val (.word accelerator)))
    (aligned : accelerator.toNat % 8 = 0) (fits : accelerator.toNat + 96 ≤ 33806089496)
    (outside : watched.toNat < accelerator.toNat ∨ accelerator.toNat + 96 ≤ watched.toNat)
    (code : state.code = originalRuntimeCode) (budget : 21 ≤ state.clock)
    (run : evaluateHOLFiniteState state shaBlockCopyCheck = (none,post)) :
    post.memory watched = state.memory watched := by
  have shifted : (accelerator + (32#64)).toNat = accelerator.toNat + 32 := by
    rw [BitVec.toNat_add_of_lt (by change accelerator.toNat + 32 < 2 ^ 64; omega)]; rfl
  have dstAligned : (accelerator + (32#64)).toNat % 8 = 0 := by rw [shifted]; omega
  have dstFits : (accelerator + (32#64)).toNat + (64#64).toNat ≤ 33806089496 := by change _ + 64 ≤ _; rw [shifted]; omega
  have dstOutside : watched.toNat < (accelerator + (32#64)).toNat ∨
      (accelerator + (32#64)).toNat + (64#64).toNat ≤ watched.toNat := by
    change watched.toNat < _ ∨ _ + 64 ≤ _
    rw [shifted]
    rcases outside with before | after
    · left; omega
    · right; omega
  have separate := memcpy_interval_separate (accelerator + (32#64)) (64#64) watched dstAligned dstFits dstOutside
  unfold shaBlockCopyCheck at run
  rw [evaluateHOLFiniteState_ite] at run
  split at run
  · split at run
    · rw [evaluateHOLFiniteState_skip] at run
      obtain ⟨_,rfl⟩ := Prod.mk.inj run
      rfl
    · exact memcpy_call_normal_memory state post _ (accelerator + (32#64)) block (64#64) watched
        (by simp [evalListHOLExact,evalHOLExact,atBlock,atAccel,wordOpHOL,wordOp,valueIsWord,valueWord]) code
        (fun offset inside => (separate offset inside).1) (fun offset inside => (separate offset inside).2)
        (by decide) budget run
  · cases run

#print axioms source_shaBlock_copy_check
#print axioms shaBlockCopy_globals
#print axioms shaBlockCopy_normal_memory
end InitECandidate.Runtime
