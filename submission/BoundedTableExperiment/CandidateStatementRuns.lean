import InitECandidate.Runtime.SourceClock
import InitECandidate.Runtime.PanCostTotal
import CandidateAst

namespace BoundedTableExperiment

open InitECandidate.Runtime
open InitECandidate.Runtime.FineCost
open Flapjack
open Flapjack.Pancake.PanLang
open Flapjack.PanSemStateFiniteExact

/-- The candidate's actual `htab_set` body has a finite size-aware
`StatementRun` from every state. -/
theorem candidate_htab_set_trace {F : Type} (fn : MlS)
    (s : PanSemStateFiniteExact 64 F) :
    ∃ events, StatementRun fn s (sourceFunctionBody Candidate.guestFn_htab_set)
      (s.evaluateHOLFiniteState (sourceFunctionBody Candidate.guestFn_htab_set)).1
      (s.evaluateHOLFiniteState (sourceFunctionBody Candidate.guestFn_htab_set)).2 events :=
  source_evaluation_cost_trace fn s _

/-- The selected candidate `htab_set` trace has the claimed source cost. -/
theorem candidate_htab_set_cost_spec {F : Type} (fn : MlS) (coeff : Work)
    (s : PanSemStateFiniteExact 64 F) :
    ∃ events, StatementRun fn s (sourceFunctionBody Candidate.guestFn_htab_set)
      (s.evaluateHOLFiniteState (sourceFunctionBody Candidate.guestFn_htab_set)).1
      (s.evaluateHOLFiniteState (sourceFunctionBody Candidate.guestFn_htab_set)).2 events ∧
      sourceExecutionCost fn coeff s (sourceFunctionBody Candidate.guestFn_htab_set) =
        coeff.score (executionWork events) :=
  sourceExecutionCost_spec fn coeff s _

/-- The candidate's actual `htab_del` body has a finite size-aware trace. -/
theorem candidate_htab_del_trace {F : Type} (fn : MlS)
    (s : PanSemStateFiniteExact 64 F) :
    ∃ events, StatementRun fn s (sourceFunctionBody Candidate.guestFn_htab_del)
      (s.evaluateHOLFiniteState (sourceFunctionBody Candidate.guestFn_htab_del)).1
      (s.evaluateHOLFiniteState (sourceFunctionBody Candidate.guestFn_htab_del)).2 events :=
  source_evaluation_cost_trace fn s _

/-- The candidate's actual `htab_truncate` body has a finite size-aware trace. -/
theorem candidate_htab_truncate_trace {F : Type} (fn : MlS)
    (s : PanSemStateFiniteExact 64 F) :
    ∃ events, StatementRun fn s (sourceFunctionBody Candidate.guestFn_htab_truncate)
      (s.evaluateHOLFiniteState (sourceFunctionBody Candidate.guestFn_htab_truncate)).1
      (s.evaluateHOLFiniteState (sourceFunctionBody Candidate.guestFn_htab_truncate)).2 events :=
  source_evaluation_cost_trace fn s _

/-- The candidate's actual `htab_grow` body has a finite size-aware trace. -/
theorem candidate_htab_grow_trace {F : Type} (fn : MlS)
    (s : PanSemStateFiniteExact 64 F) :
    ∃ events, StatementRun fn s (sourceFunctionBody Candidate.guestFn_htab_grow)
      (s.evaluateHOLFiniteState (sourceFunctionBody Candidate.guestFn_htab_grow)).1
      (s.evaluateHOLFiniteState (sourceFunctionBody Candidate.guestFn_htab_grow)).2 events :=
  source_evaluation_cost_trace fn s _

/-- The candidate's actual `htab_copy` body has a finite size-aware trace. -/
theorem candidate_htab_copy_trace {F : Type} (fn : MlS)
    (s : PanSemStateFiniteExact 64 F) :
    ∃ events, StatementRun fn s (sourceFunctionBody Candidate.guestFn_htab_copy)
      (s.evaluateHOLFiniteState (sourceFunctionBody Candidate.guestFn_htab_copy)).1
      (s.evaluateHOLFiniteState (sourceFunctionBody Candidate.guestFn_htab_copy)).2 events :=
  source_evaluation_cost_trace fn s _

/-- The candidate's actual `htab_find_leaf_path` body has a finite size-aware
trace. -/
theorem candidate_htab_find_leaf_path_trace {F : Type} (fn : MlS)
    (s : PanSemStateFiniteExact 64 F) :
    ∃ events, StatementRun fn s (sourceFunctionBody Candidate.guestFn_htab_find_leaf_path)
      (s.evaluateHOLFiniteState (sourceFunctionBody Candidate.guestFn_htab_find_leaf_path)).1
      (s.evaluateHOLFiniteState (sourceFunctionBody Candidate.guestFn_htab_find_leaf_path)).2 events :=
  source_evaluation_cost_trace fn s _

/-- Selected cost spec for the candidate `htab_del`. -/
theorem candidate_htab_del_cost_spec {F : Type} (fn : MlS) (coeff : Work)
    (s : PanSemStateFiniteExact 64 F) :
    ∃ events, StatementRun fn s (sourceFunctionBody Candidate.guestFn_htab_del)
      (s.evaluateHOLFiniteState (sourceFunctionBody Candidate.guestFn_htab_del)).1
      (s.evaluateHOLFiniteState (sourceFunctionBody Candidate.guestFn_htab_del)).2 events ∧
      sourceExecutionCost fn coeff s (sourceFunctionBody Candidate.guestFn_htab_del) =
        coeff.score (executionWork events) :=
  sourceExecutionCost_spec fn coeff s _

/-- Selected cost spec for the candidate `htab_truncate`. -/
theorem candidate_htab_truncate_cost_spec {F : Type} (fn : MlS) (coeff : Work)
    (s : PanSemStateFiniteExact 64 F) :
    ∃ events, StatementRun fn s (sourceFunctionBody Candidate.guestFn_htab_truncate)
      (s.evaluateHOLFiniteState (sourceFunctionBody Candidate.guestFn_htab_truncate)).1
      (s.evaluateHOLFiniteState (sourceFunctionBody Candidate.guestFn_htab_truncate)).2 events ∧
      sourceExecutionCost fn coeff s (sourceFunctionBody Candidate.guestFn_htab_truncate) =
        coeff.score (executionWork events) :=
  sourceExecutionCost_spec fn coeff s _

/-- Selected cost spec for the candidate `htab_grow`. -/
theorem candidate_htab_grow_cost_spec {F : Type} (fn : MlS) (coeff : Work)
    (s : PanSemStateFiniteExact 64 F) :
    ∃ events, StatementRun fn s (sourceFunctionBody Candidate.guestFn_htab_grow)
      (s.evaluateHOLFiniteState (sourceFunctionBody Candidate.guestFn_htab_grow)).1
      (s.evaluateHOLFiniteState (sourceFunctionBody Candidate.guestFn_htab_grow)).2 events ∧
      sourceExecutionCost fn coeff s (sourceFunctionBody Candidate.guestFn_htab_grow) =
        coeff.score (executionWork events) :=
  sourceExecutionCost_spec fn coeff s _

/-- Selected cost spec for the candidate `htab_copy`. -/
theorem candidate_htab_copy_cost_spec {F : Type} (fn : MlS) (coeff : Work)
    (s : PanSemStateFiniteExact 64 F) :
    ∃ events, StatementRun fn s (sourceFunctionBody Candidate.guestFn_htab_copy)
      (s.evaluateHOLFiniteState (sourceFunctionBody Candidate.guestFn_htab_copy)).1
      (s.evaluateHOLFiniteState (sourceFunctionBody Candidate.guestFn_htab_copy)).2 events ∧
      sourceExecutionCost fn coeff s (sourceFunctionBody Candidate.guestFn_htab_copy) =
        coeff.score (executionWork events) :=
  sourceExecutionCost_spec fn coeff s _

/-- The candidate's actual whole `main` body has a finite size-aware trace. -/
theorem candidate_main_trace {F : Type} (fn : MlS)
    (s : PanSemStateFiniteExact 64 F) :
    ∃ events, StatementRun fn s (sourceFunctionBody Candidate.guestFn_main)
      (s.evaluateHOLFiniteState (sourceFunctionBody Candidate.guestFn_main)).1
      (s.evaluateHOLFiniteState (sourceFunctionBody Candidate.guestFn_main)).2 events :=
  source_evaluation_cost_trace fn s _

end BoundedTableExperiment

#print axioms BoundedTableExperiment.candidate_htab_set_cost_spec
#print axioms BoundedTableExperiment.candidate_htab_del_trace
#print axioms BoundedTableExperiment.candidate_main_trace
