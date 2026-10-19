import InitECandidate.Runtime.HashProbeActiveOccupied
import InitECandidate.Runtime.HtabFindSlotReturned
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- A returning actual lookup iteration returns its probed index, which the
enabled occupancy guard proves occupied. No assumptions about query bytes enter. -/
theorem hash_find_iteration_returned_occupied {F : Type} (s post : PanSemStateFiniteExact 64 F)
    (index used active : BitVec 64) (value : ValueHOL 64)
    (atIndex : s.locals.lookup (ofString "i") = some (.val (.word index)))
    (atUsed : s.locals.lookup (ofString "used") = some (.val (.word used)))
    (condition : evalHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a))
      (hashProbeOccupied (ofString "i")) = some (.val (.word active)))
    (nonzero : active ≠ 0)
    (run : evaluateHOLFiniteState s hashFindIteration = (some (.returned value),post)) :
    value = .val (.word index) ∧ hashOccupancyRead s used index ≠ some 0 := by
  have occupied := hash_probe_active_occupied s (ofString "i") index used active atIndex atUsed condition nonzero
  unfold hashFindIteration at run
  obtain ⟨resumed,inner,locals,returned⟩ := decCall_returned_locals run
  have same := hashFindDecision_returned resumed inner index value
    (by rw [locals _ (by decide)]; exact atIndex) returned
  exact ⟨same,occupied⟩

#print axioms hash_find_iteration_returned_occupied
end InitECandidate.Runtime
