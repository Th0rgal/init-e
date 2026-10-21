import ActualCandidateHeaderStore
import InitECandidate.Runtime.GuestCostChargeFamily

namespace BoundedTableExperiment

open InitECandidate.Runtime
open InitECandidate.Runtime.FineCost
open Flapjack
open Flapjack.Pancake.PanLang
open Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

set_option maxHeartbeats 2000000

/-- Costed run of a header address `t + offset`. -/
theorem candidate_header_address_run {F : Type} (s : PanSemStateFiniteExact 64 F)
    (tbase : BitVec 64) (offset : Nat)
    (tLocal : s.locals.lookup (ofString "t") = some (.val (.word tbase))) :
    CostedExpressionRun s
      (.op .add [.var .local (ofString "t"), .const (BitVec.ofNat 64 offset)])
      (some (.val (.word (tbase + BitVec.ofNat 64 offset))))
      (expressionEvents s
        (.op .add [.var .local (ofString "t"), .const (BitVec.ofNat 64 offset)])) := by
  apply costedExpression_events
  simp [expressionValue, evalHOLExact, evalListHOLExact, tLocal, valueIsWord, wordOpHOL,
    wordOp, valueWord]

/-- Costed run of a word-valued local. -/
theorem candidate_header_local_run {F : Type} (s : PanSemStateFiniteExact 64 F)
    (name : MlS) (value : BitVec 64)
    (localEq : s.locals.lookup name = some (.val (.word value))) :
    CostedExpressionRun s (.var .local name) (some (.val (.word value)))
      (expressionEvents s (.var .local name)) := by
  apply costedExpression_events
  simp [expressionValue, evalHOLExact, evalListHOLExact, localEq, valueIsWord]

/-- Costed run of a constant word. -/
theorem candidate_header_const_run {F : Type} (s : PanSemStateFiniteExact 64 F)
    (value : BitVec 64) :
    CostedExpressionRun s (.const value) (some (.val (.word value)))
      (expressionEvents s (.const value)) := by
  apply costedExpression_events
  simp [expressionValue, evalHOLExact, evalListHOLExact, valueIsWord]

end BoundedTableExperiment

#print axioms BoundedTableExperiment.candidate_header_address_run
#print axioms BoundedTableExperiment.candidate_header_local_run
#print axioms BoundedTableExperiment.candidate_header_const_run

namespace BoundedTableExperiment

open InitECandidate.Runtime
open InitECandidate.Runtime.FineCost
open Flapjack
open Flapjack.Pancake.PanLang
open Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- Memory after the four candidate header stores at offsets 0, 8, 16, 24. -/
noncomputable def candidateHeaderFourMemory {F : Type}
    (s : PanSemStateFiniteExact 64 F)
    (a0 v0 a1 v1 a2 v2 a3 v3 : BitVec 64) :
    RiscV.Word 64 → HolWordLab 64 :=
  candidateHeaderMemory
    { s with memory :=
        (candidateHeaderMemory
          { s with memory :=
            (candidateHeaderMemory
              { s with memory := (candidateHeaderMemory s a0 v0) } a1 v1) } a2 v2) } a3 v3

/-- The four candidate header stores run through to an opaque continuation,
writing key_len, stride, cap and zero at t+0/8/16/24. -/
theorem candidate_header_four_stores {F : Type} (fn : MlS)
    (s : PanSemStateFiniteExact 64 F)
    (tbase keyLen stride cap : BitVec 64)
    (tLocal : s.locals.lookup (ofString "t") = some (.val (.word tbase)))
    (keyLocal : s.locals.lookup (ofString "key_len") = some (.val (.word keyLen)))
    (strideLocal : s.locals.lookup (ofString "stride") = some (.val (.word stride)))
    (capLocal : s.locals.lookup (ofString "cap") = some (.val (.word cap)))
    (d0 : s.memaddrs (tbase + BitVec.ofNat 64 0))
    (d1 : s.memaddrs (tbase + BitVec.ofNat 64 8))
    (d2 : s.memaddrs (tbase + BitVec.ofNat 64 16))
    (d3 : s.memaddrs (tbase + BitVec.ofNat 64 24)) :
    ∃ final events, StatementRun fn s
      (.seq (.store (.op .add [.var .local (ofString "t"), .const (BitVec.ofNat 64 0)])
              (.var .local (ofString "key_len")))
        (.seq (.store (.op .add [.var .local (ofString "t"), .const (BitVec.ofNat 64 8)])
                (.var .local (ofString "stride")))
          (.seq (.store (.op .add [.var .local (ofString "t"), .const (BitVec.ofNat 64 16)])
                  (.var .local (ofString "cap")))
            (.seq (.store (.op .add [.var .local (ofString "t"), .const (BitVec.ofNat 64 24)])
                    (.const (BitVec.ofNat 64 0))) .skip))))
      none final events := by
  let a0e := (expressionEvents s
    (.op .add [.var .local (ofString "t"), .const (BitVec.ofNat 64 0)]))
  let v0e := expressionEvents s (.var .local (ofString "key_len"))
  let d0r : CostedExpressionRun s
      (.op .add [.var .local (ofString "t"), .const (BitVec.ofNat 64 0)])
      (some (.val (.word (tbase + BitVec.ofNat 64 0)))) a0e :=
    candidate_header_address_run s tbase 0 tLocal
  let v0r : CostedExpressionRun s (.var .local (ofString "key_len"))
      (some (.val (.word keyLen))) v0e :=
    candidate_header_local_run s (ofString "key_len") keyLen keyLocal
  have h0 := candidate_header_store_word fn s
    (.op .add [.var .local (ofString "t"), .const (BitVec.ofNat 64 0)])
    (.var .local (ofString "key_len")) (tbase + BitVec.ofNat 64 0) keyLen a0e v0e d0r v0r d0
  let s1 := { s with memory := candidateHeaderMemory s (tbase + BitVec.ofNat 64 0) keyLen }
  have t1 : s1.locals.lookup (ofString "t") = some (.val (.word tbase)) := tLocal
  have st1 : s1.locals.lookup (ofString "stride") = some (.val (.word stride)) := strideLocal
  have c1 : s1.locals.lookup (ofString "cap") = some (.val (.word cap)) := capLocal
  let a1e := expressionEvents s1
    (.op .add [.var .local (ofString "t"), .const (BitVec.ofNat 64 8)])
  let v1e := expressionEvents s1 (.var .local (ofString "stride"))
  let d1r : CostedExpressionRun s1
      (.op .add [.var .local (ofString "t"), .const (BitVec.ofNat 64 8)])
      (some (.val (.word (tbase + BitVec.ofNat 64 8)))) a1e :=
    candidate_header_address_run s1 tbase 8 t1
  let v1r : CostedExpressionRun s1 (.var .local (ofString "stride"))
      (some (.val (.word stride))) v1e :=
    candidate_header_local_run s1 (ofString "stride") stride st1
  have h1 := candidate_header_store_word fn s1
    (.op .add [.var .local (ofString "t"), .const (BitVec.ofNat 64 8)])
    (.var .local (ofString "stride")) (tbase + BitVec.ofNat 64 8) stride a1e v1e d1r v1r
    (by simpa [s1] using d1)
  let s2 := { s1 with memory := candidateHeaderMemory s1 (tbase + BitVec.ofNat 64 8) stride }
  have t2 : s2.locals.lookup (ofString "t") = some (.val (.word tbase)) := t1
  have c2 : s2.locals.lookup (ofString "cap") = some (.val (.word cap)) := c1
  let a2e := expressionEvents s2
    (.op .add [.var .local (ofString "t"), .const (BitVec.ofNat 64 16)])
  let v2e := expressionEvents s2 (.var .local (ofString "cap"))
  let d2r : CostedExpressionRun s2
      (.op .add [.var .local (ofString "t"), .const (BitVec.ofNat 64 16)])
      (some (.val (.word (tbase + BitVec.ofNat 64 16)))) a2e :=
    candidate_header_address_run s2 tbase 16 t2
  let v2r : CostedExpressionRun s2 (.var .local (ofString "cap"))
      (some (.val (.word cap))) v2e :=
    candidate_header_local_run s2 (ofString "cap") cap c2
  have h2 := candidate_header_store_word fn s2
    (.op .add [.var .local (ofString "t"), .const (BitVec.ofNat 64 16)])
    (.var .local (ofString "cap")) (tbase + BitVec.ofNat 64 16) cap a2e v2e d2r v2r
    (by simpa [s2, s1] using d2)
  let s3 := { s2 with memory := candidateHeaderMemory s2 (tbase + BitVec.ofNat 64 16) cap }
  have t3 : s3.locals.lookup (ofString "t") = some (.val (.word tbase)) := t2
  let a3e := expressionEvents s3
    (.op .add [.var .local (ofString "t"), .const (BitVec.ofNat 64 24)])
  let v3e := expressionEvents s3 (.const (BitVec.ofNat 64 0))
  let d3r : CostedExpressionRun s3
      (.op .add [.var .local (ofString "t"), .const (BitVec.ofNat 64 24)])
      (some (.val (.word (tbase + BitVec.ofNat 64 24)))) a3e :=
    candidate_header_address_run s3 tbase 24 t3
  let v3r : CostedExpressionRun s3 (.const (BitVec.ofNat 64 0))
      (some (.val (.word (BitVec.ofNat 64 0)))) v3e :=
    candidate_header_const_run s3 (BitVec.ofNat 64 0)
  have h3 := candidate_header_store_word fn s3
    (.op .add [.var .local (ofString "t"), .const (BitVec.ofNat 64 24)])
    (.const (BitVec.ofNat 64 0)) (tbase + BitVec.ofNat 64 24) (BitVec.ofNat 64 0) a3e v3e d3r v3r
    (by simpa [s3, s2, s1] using d3)
  refine ⟨_, _, StatementRun.seqNext h0
    (StatementRun.seqNext h1 (StatementRun.seqNext h2
      (StatementRun.seqNext h3 (StatementRun.skip _))))⟩

end BoundedTableExperiment

#print axioms BoundedTableExperiment.candidate_header_four_stores

namespace BoundedTableExperiment

open InitECandidate.Runtime
open InitECandidate.Runtime.FineCost
open Flapjack
open Flapjack.Pancake.PanLang
open Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- State after the four candidate header stores. -/
noncomputable def candidateHeaderFinalState {F : Type}
    (s : PanSemStateFiniteExact 64 F)
    (a0 v0 a1 v1 a2 v2 a3 v3 : BitVec 64) : PanSemStateFiniteExact 64 F :=
  let s1 := { s with memory := candidateHeaderMemory s a0 v0 }
  let s2 := { s1 with memory := candidateHeaderMemory s1 a1 v1 }
  let s3 := { s2 with memory := candidateHeaderMemory s2 a2 v2 }
  { s3 with memory := candidateHeaderMemory s3 a3 v3 }

/-- The four candidate header stores run through to an opaque continuation. -/
theorem candidate_header_four_stores_rest {F : Type} (fn : MlS)
    (s final : PanSemStateFiniteExact 64 F) (rest : ProgHOL 64)
    (result : Option (PanSemResultExact 64)) (restEvents : List WorkEvent)
    (tbase keyLen stride cap : BitVec 64)
    (tLocal : s.locals.lookup (ofString "t") = some (.val (.word tbase)))
    (keyLocal : s.locals.lookup (ofString "key_len") = some (.val (.word keyLen)))
    (strideLocal : s.locals.lookup (ofString "stride") = some (.val (.word stride)))
    (capLocal : s.locals.lookup (ofString "cap") = some (.val (.word cap)))
    (d0 : s.memaddrs (tbase + BitVec.ofNat 64 0))
    (d1 : s.memaddrs (tbase + BitVec.ofNat 64 8))
    (d2 : s.memaddrs (tbase + BitVec.ofNat 64 16))
    (d3 : s.memaddrs (tbase + BitVec.ofNat 64 24))
    (restRun : StatementRun fn
      (candidateHeaderFinalState s
        (tbase + BitVec.ofNat 64 0) keyLen
        (tbase + BitVec.ofNat 64 8) stride
        (tbase + BitVec.ofNat 64 16) cap
        (tbase + BitVec.ofNat 64 24) (BitVec.ofNat 64 0)) rest result final restEvents) :
    ∃ events, StatementRun fn s
      (.seq (.store (.op .add [.var .local (ofString "t"), .const (BitVec.ofNat 64 0)])
              (.var .local (ofString "key_len")))
        (.seq (.store (.op .add [.var .local (ofString "t"), .const (BitVec.ofNat 64 8)])
                (.var .local (ofString "stride")))
          (.seq (.store (.op .add [.var .local (ofString "t"), .const (BitVec.ofNat 64 16)])
                  (.var .local (ofString "cap")))
            (.seq (.store (.op .add [.var .local (ofString "t"), .const (BitVec.ofNat 64 24)])
                    (.const (BitVec.ofNat 64 0))) rest))))
      result final events := by
  let a0e := (expressionEvents s
    (.op .add [.var .local (ofString "t"), .const (BitVec.ofNat 64 0)]))
  let v0e := expressionEvents s (.var .local (ofString "key_len"))
  let d0r : CostedExpressionRun s
      (.op .add [.var .local (ofString "t"), .const (BitVec.ofNat 64 0)])
      (some (.val (.word (tbase + BitVec.ofNat 64 0)))) a0e :=
    candidate_header_address_run s tbase 0 tLocal
  let v0r : CostedExpressionRun s (.var .local (ofString "key_len"))
      (some (.val (.word keyLen))) v0e :=
    candidate_header_local_run s (ofString "key_len") keyLen keyLocal
  have h0 := candidate_header_store_word fn s
    (.op .add [.var .local (ofString "t"), .const (BitVec.ofNat 64 0)])
    (.var .local (ofString "key_len")) (tbase + BitVec.ofNat 64 0) keyLen a0e v0e d0r v0r d0
  let s1 := { s with memory := candidateHeaderMemory s (tbase + BitVec.ofNat 64 0) keyLen }
  have t1 : s1.locals.lookup (ofString "t") = some (.val (.word tbase)) := tLocal
  have st1 : s1.locals.lookup (ofString "stride") = some (.val (.word stride)) := strideLocal
  have c1 : s1.locals.lookup (ofString "cap") = some (.val (.word cap)) := capLocal
  let a1e := expressionEvents s1
    (.op .add [.var .local (ofString "t"), .const (BitVec.ofNat 64 8)])
  let v1e := expressionEvents s1 (.var .local (ofString "stride"))
  let d1r : CostedExpressionRun s1
      (.op .add [.var .local (ofString "t"), .const (BitVec.ofNat 64 8)])
      (some (.val (.word (tbase + BitVec.ofNat 64 8)))) a1e :=
    candidate_header_address_run s1 tbase 8 t1
  let v1r : CostedExpressionRun s1 (.var .local (ofString "stride"))
      (some (.val (.word stride))) v1e :=
    candidate_header_local_run s1 (ofString "stride") stride st1
  have h1 := candidate_header_store_word fn s1
    (.op .add [.var .local (ofString "t"), .const (BitVec.ofNat 64 8)])
    (.var .local (ofString "stride")) (tbase + BitVec.ofNat 64 8) stride a1e v1e d1r v1r
    (by simpa [s1] using d1)
  let s2 := { s1 with memory := candidateHeaderMemory s1 (tbase + BitVec.ofNat 64 8) stride }
  have t2 : s2.locals.lookup (ofString "t") = some (.val (.word tbase)) := t1
  have c2 : s2.locals.lookup (ofString "cap") = some (.val (.word cap)) := c1
  let a2e := expressionEvents s2
    (.op .add [.var .local (ofString "t"), .const (BitVec.ofNat 64 16)])
  let v2e := expressionEvents s2 (.var .local (ofString "cap"))
  let d2r : CostedExpressionRun s2
      (.op .add [.var .local (ofString "t"), .const (BitVec.ofNat 64 16)])
      (some (.val (.word (tbase + BitVec.ofNat 64 16)))) a2e :=
    candidate_header_address_run s2 tbase 16 t2
  let v2r : CostedExpressionRun s2 (.var .local (ofString "cap"))
      (some (.val (.word cap))) v2e :=
    candidate_header_local_run s2 (ofString "cap") cap c2
  have h2 := candidate_header_store_word fn s2
    (.op .add [.var .local (ofString "t"), .const (BitVec.ofNat 64 16)])
    (.var .local (ofString "cap")) (tbase + BitVec.ofNat 64 16) cap a2e v2e d2r v2r
    (by simpa [s2, s1] using d2)
  let s3 := { s2 with memory := candidateHeaderMemory s2 (tbase + BitVec.ofNat 64 16) cap }
  have t3 : s3.locals.lookup (ofString "t") = some (.val (.word tbase)) := t2
  let a3e := expressionEvents s3
    (.op .add [.var .local (ofString "t"), .const (BitVec.ofNat 64 24)])
  let v3e := expressionEvents s3 (.const (BitVec.ofNat 64 0))
  let d3r : CostedExpressionRun s3
      (.op .add [.var .local (ofString "t"), .const (BitVec.ofNat 64 24)])
      (some (.val (.word (tbase + BitVec.ofNat 64 24)))) a3e :=
    candidate_header_address_run s3 tbase 24 t3
  let v3r : CostedExpressionRun s3 (.const (BitVec.ofNat 64 0))
      (some (.val (.word (BitVec.ofNat 64 0)))) v3e :=
    candidate_header_const_run s3 (BitVec.ofNat 64 0)
  have h3 := candidate_header_store_word fn s3
    (.op .add [.var .local (ofString "t"), .const (BitVec.ofNat 64 24)])
    (.const (BitVec.ofNat 64 0)) (tbase + BitVec.ofNat 64 24) (BitVec.ofNat 64 0) a3e v3e d3r v3r
    (by simpa [s3, s2, s1] using d3)
  have rest' : StatementRun fn
      (candidateHeaderFinalState s
        (tbase + BitVec.ofNat 64 0) keyLen
        (tbase + BitVec.ofNat 64 8) stride
        (tbase + BitVec.ofNat 64 16) cap
        (tbase + BitVec.ofNat 64 24) (BitVec.ofNat 64 0)) rest result final restEvents :=
    restRun
  have stateEq : { s3 with memory :=
      candidateHeaderMemory s3 (tbase + BitVec.ofNat 64 24) (BitVec.ofNat 64 0) } =
      candidateHeaderFinalState s
        (tbase + BitVec.ofNat 64 0) keyLen
        (tbase + BitVec.ofNat 64 8) stride
        (tbase + BitVec.ofNat 64 16) cap
        (tbase + BitVec.ofNat 64 24) (BitVec.ofNat 64 0) := by
    simp [candidateHeaderFinalState, s1, s2, s3]
  have rest'' : StatementRun fn
      { s3 with memory :=
        candidateHeaderMemory s3 (tbase + BitVec.ofNat 64 24) (BitVec.ofNat 64 0) }
      rest result final restEvents := by
    rw [stateEq]
    exact rest'
  exact ⟨_, StatementRun.seqNext h0
    (StatementRun.seqNext h1 (StatementRun.seqNext h2
      (StatementRun.seqNext h3 rest'')))⟩

end BoundedTableExperiment

#print axioms BoundedTableExperiment.candidate_header_four_stores_rest
