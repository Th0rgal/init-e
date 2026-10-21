import ActualCandidateKeysHead
import InitECandidate.Runtime.GuestCostChargeFamily

namespace BoundedTableExperiment

open InitECandidate.Runtime
open InitECandidate.Runtime.FineCost
open Flapjack
open Flapjack.Pancake.PanLang
open Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- The actual stride initializer `(key_len + 7) & (0 - 8)` evaluates to a
word. -/
theorem candidate_strideExpr_eval {F : Type} (s : PanSemStateFiniteExact 64 F)
    (keyLen : BitVec 64)
    (keyLocal : s.locals.lookup (ofString "key_len") = some (.val (.word keyLen))) :
    @evalHOLExact 64 F _ s.toExact (fun address => Classical.propDecidable (s.memaddrs address))
      strideExpr = some (.val (.word ((keyLen + BitVec.ofNat 64 7) &&&
        (BitVec.ofNat 64 0 - BitVec.ofNat 64 8)))) := by
  simp [strideExpr, evalHOLExact, evalListHOLExact, PanSemStateFiniteExact.toExact, keyLocal,
    valueIsWord, wordOp, wordOpHOL, panOpHOL, AndOp.and, valueWord]

end BoundedTableExperiment

#print axioms BoundedTableExperiment.candidate_strideExpr_eval

namespace BoundedTableExperiment

open InitECandidate.Runtime
open InitECandidate.Runtime.FineCost
open Flapjack
open Flapjack.Pancake.PanLang
open Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- The actual candidate stride is 8-byte aligned. -/
theorem candidate_stride_aligned (keyLen : BitVec 64) :
    ((keyLen + BitVec.ofNat 64 7) &&& (BitVec.ofNat 64 0 - BitVec.ofNat 64 8)) &&&
        BitVec.ofNat 64 7 = 0 := by
  rw [BitVec.and_assoc]
  have h : (BitVec.ofNat 64 0 - BitVec.ofNat 64 8) &&& BitVec.ofNat 64 7 = 0 := by decide
  simp [h]

end BoundedTableExperiment

#print axioms BoundedTableExperiment.candidate_stride_aligned
