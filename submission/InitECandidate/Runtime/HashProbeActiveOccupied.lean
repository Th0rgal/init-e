import InitECandidate.Runtime.HashProbeSource
import InitECandidate.Runtime.HashProbeCapacity
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- A successfully enabled actual probe condition rules out an empty occupancy
byte. This partial-correctness fact needs no query-key alignment or readability. -/
theorem hash_probe_active_occupied {F : Type} (s : PanSemStateFiniteExact 64 F)
    (name : MlS) (index used active : BitVec 64)
    (atIndex : s.locals.lookup name = some (.val (.word index)))
    (atUsed : s.locals.lookup (ofString "used") = some (.val (.word used)))
    (evaluated : evalHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a))
      (hashProbeOccupied name) = some (.val (.word active)))
    (nonzero : active ≠ 0) : hashOccupancyRead s used index ≠ some 0 := by
  intro empty
  have loaded : @panMemLoadByteHOL 64 _ s.memory s.memaddrs
      (fun a => Classical.propDecidable (s.memaddrs a)) s.be (used + index) = some (0 : UInt8) := empty
  have zero := eval_hashProbeOccupied s name index used 0 atIndex atUsed loaded
  have actualZero : evalHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a))
      (hashProbeOccupied name) = some (.val (.word (0#64))) := by
    simpa [evalHOLFinite_eq_toExact,Compiler.Encoders.Asm.wordCmpHOL] using zero
  rw [actualZero] at evaluated
  have same : active = 0 := HolWordLab.word.inj (ValueHOL.val.inj (Option.some.inj evaluated.symm))
  exact nonzero same

#print axioms hash_probe_active_occupied
end InitECandidate.Runtime
