import CandidateFindLeafShape
import PathStatementCoupling
import ActualPathMemoryInvariant

set_option maxHeartbeats 1000000

namespace BoundedTableExperiment

open InitECandidate.Runtime
open InitECandidate.Runtime.FineCost
open Flapjack
open Flapjack.Pancake.PanLang
open Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- Actual `storeValue` run of the candidate path push. -/
theorem candidateFindLeafPush_run {F : Type} {fn : MlS}
    {s : PanSemStateFiniteExact 64 F}
    {address value : BitVec 64} {addressEvents valueEvents : List WorkEvent}
    {mem : BitVec 64 → HolWordLab 64}
    (dst : CostedExpressionRun s
      (.op .add [.var .local (ofString "path"),
        .panop .mul [.var .local (ofString "depth"), .const (BitVec.ofNat 64 8)]])
      (some (ValueHOL.val (HolWordLab.word address))) addressEvents)
    (src : CostedExpressionRun s (.var .local (ofString "node"))
      (some (.val (.word value))) valueEvents)
    (write : @panMemStoresHOL 64 _ address
      (flattenHOL (.val (.word value))) s.memaddrs
      (Classical.decPred _) s.memory = some mem) :
    StatementRun fn s candidateFindLeafPush none { s with memory := mem }
      (.statement :: (addressEvents ++ valueEvents ++
        [.memory (flattenHOL (.val (.word value))).length,
         .cost (storeOverhead (flattenHOL (.val (.word value))).length)])) := by
  show StatementRun fn s
    (.store (.op .add [.var .local (ofString "path"),
        .panop .mul [.var .local (ofString "depth"), .const (BitVec.ofNat 64 8)]])
      (.var .local (ofString "node"))) none { s with memory := mem } _
  exact StatementRun.storeValue dst src write

/-- Actual event score of the candidate path push, one word. -/
theorem candidateFindLeafPush_score {F : Type} {fn : MlS} (coeff : Work)
    {s : PanSemStateFiniteExact 64 F}
    {address value : BitVec 64} {addressEvents valueEvents : List WorkEvent}
    {mem : BitVec 64 → HolWordLab 64}
    (dst : CostedExpressionRun s
      (.op .add [.var .local (ofString "path"),
        .panop .mul [.var .local (ofString "depth"), .const (BitVec.ofNat 64 8)]])
      (some (ValueHOL.val (HolWordLab.word address))) addressEvents)
    (src : CostedExpressionRun s (.var .local (ofString "node"))
      (some (.val (.word value))) valueEvents)
    (write : @panMemStoresHOL 64 _ address
      (flattenHOL (.val (.word value))) s.memaddrs
      (Classical.decPred _) s.memory = some mem) :
    coeff.score (executionWork
        (.statement :: (addressEvents ++ valueEvents ++
          [.memory (flattenHOL (.val (.word value))).length,
           .cost (storeOverhead (flattenHOL (.val (.word value))).length)]))) =
      coeff.statements + coeff.score (executionWork addressEvents) +
      coeff.score (executionWork valueEvents) + coeff.memoryAccesses +
      coeff.nativeCost * storeOverhead 1 := by
  have hlen : (flattenHOL (.val (.word value))).length = 1 := by
    rw [flattenHOL.eq_1]
    rfl
  simpa [hlen, List.append_assoc] using
    path_store_one_word_score (fn := fn) coeff dst src write hlen

/-- The actual candidate path push preserves and extends `PathMemoryInv`. -/
theorem candidateFindLeafPush_preserves {F : Type}
    {s : PanSemStateFiniteExact 64 F} {base : BitVec 64} {depth : Nat}
    {routes : Nat → BitVec 64} (inv : PathMemoryInv s base depth routes)
    (bound : depth < 2 ^ 61) (hdom : s.memaddrs (pathAddr base depth))
    {address value : BitVec 64} {mem : BitVec 64 → HolWordLab 64}
    (haddr : address = pathAddr base depth)
    (write : @panMemStoresHOL 64 _ address [.word value] s.memaddrs
      (Classical.decPred _) s.memory = some mem) :
    PathMemoryInv { s with memory := mem } base (depth + 1)
      (fun i => if i = depth then value else routes i) :=
  PathMemoryInv.push_at inv bound hdom haddr write

end BoundedTableExperiment

#print axioms BoundedTableExperiment.candidateFindLeafPush_preserves

#print axioms BoundedTableExperiment.candidateFindLeafPush_run
#print axioms BoundedTableExperiment.candidateFindLeafPush_score
