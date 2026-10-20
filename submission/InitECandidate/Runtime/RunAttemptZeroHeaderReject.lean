import InitECandidate.Runtime.RunAttemptHeadersSource
import InitECandidate.Runtime.RunAttemptHeadersEntry
import InitECandidate.Runtime.BoundedDecCallReach
import InitECandidate.Runtime.ValidateHeadersZeroBody
import InitECandidate.Runtime.RunAttemptHeaderCountReach
/-!
The actual zero-header early reject.

A canonically decoded empty header array gives header count `0`, so the main header-bound table
premise is unavailable and this path must be proved directly from the typed record cells and the
typed capped heap.  This module covers the caller's own part of that path: the real count reload
and the empty-header guard terminate in `BlockErr 3` before the parent load, with no source tick
and without any header table premise.
-/
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
set_option maxRecDepth 100000
set_option maxHeartbeats 800000

/-- **The empty-header guard is terminal.**  At `runAttemptAt 3`, with the typed `si` record cell
`si+80` still holding the zero header count, the actual count reload binds `nh := 0` and the guard
raises `BlockErr 3`; the whole prefix is a terminal abort within eight source ticks, and the parent
load at `runAttemptAt 5` is never reached. -/
theorem run_attempt_zero_header_guard_aborts {F : Type} (s : PanSemStateFiniteExact 64 F)
    (si : BitVec 64)
    (atSi : s.locals.lookup (ofString "si") = some (.val (.word si)))
    (domain : s.memaddrs (si + (80#64)))
    (cell : s.memory (si + (80#64)) = .word (0 : BitVec 64)) :
    StAbort s (evaluateHOLFiniteState s (runAttemptAt 3)) 0 := by
  have loaded := run_attempt_header_count_reaches s si (0 : BitVec 64) atSi domain cell
  have aborted : Reaches s (runAttemptAt 3) (fun _ => False) 0 (runAttemptAt 5) := by
    refine reaches_trans s (runAttemptAt 3) (runAttemptAt 4) (runAttemptAt 5) _ (fun _ => False) 0 0
      loaded ?_
    intro next same
    subst next
    have atCount : (setVarHOLFinite (ofString "nh") (.val (.word (0 : BitVec 64))) s).locals.lookup
        (ofString "nh") = some (.val (.word (0 : BitVec 64))) := by
      simp [setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]
    have guarded := run_attempt_header_guard_reaches
      (setVarHOLFinite (ofString "nh") (.val (.word (0 : BitVec 64))) s) (0 : BitVec 64) atCount
    refine reaches_mono _ (runAttemptAt 4) (runAttemptAt 5) _ (fun _ => False) 0 0 (le_refl _) ?_
      guarded
    intro ready facts
    exact facts.2 rfl
  rcases aborted with ⟨next,facts,_,_,_⟩ | done
  · exact facts.elim
  · exact done

#print axioms run_attempt_zero_header_guard_aborts
end InitECandidate.Runtime
