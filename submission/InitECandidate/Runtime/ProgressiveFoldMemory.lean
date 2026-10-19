import InitECandidate.Runtime.ProgressiveSuffixBound
import InitECandidate.Runtime.Sha256PairMemory
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

theorem progressiveFold_tail_normal_memory {F : Type} (state post : PanSemStateFiniteExact 64 F)
    (pointer accelerator roots acc k watched : BitVec 64)
    (atPointer : state.globals.lookup (ofString "sha_st") = some (.val (.word pointer)))
    (atAccel : state.globals.lookup (ofString "sha_accel") = some (.val (.word accelerator)))
    (atRoots : state.locals.lookup (ofString "roots") = some (.val (.word roots)))
    (atAcc : state.locals.lookup (ofString "acc") = some (.val (.word acc)))
    (atK : state.locals.lookup (ofString "k") = some (.val (.word k)))
    (accAligned : acc.toNat % 8 = 0) (accFits : acc.toNat + 32 ≤ 33806089496)
    (accBefore : watched.toNat < acc.toNat)
    (accelAligned : accelerator.toNat % 8 = 0)
    (accelFits : accelerator.toNat + 96 ≤ 33806089496) (pointerFits : pointer.toNat + 64 ≤ 33806089496)
    (accelOutside : watched.toNat < accelerator.toNat ∨ accelerator.toNat + 96 ≤ watched.toNat)
    (pointerOutside : watched.toNat < pointer.toNat ∨ pointer.toNat + 64 ≤ watched.toNat)
    (code : state.code = originalRuntimeCode) (budget : 119 ≤ state.clock)
    (run : evaluateHOLFiniteState state progressiveFoldTail = (none,post)) :
    post.memory watched = state.memory watched := by
  exact shaPair_call_normal_memory state post _ pointer accelerator acc (roots + k * (32#64)) acc watched
    (by simp [progressiveFoldTail,evalListHOLExact,evalHOLExact,atRoots,atAcc,atK,wordOpHOL,wordOp,
      valueIsWord,valueWord,panOpHOL]) atPointer atAccel accelAligned accAligned accelFits pointerFits accFits
    accelOutside pointerOutside (Or.inl accBefore) code budget run

#print axioms progressiveFold_tail_normal_memory
end InitECandidate.Runtime
