import InitECandidate.Runtime.RunAttemptInitialReach
import InitECandidate.Runtime.RunAttemptZeroHeaderReject
/-!
The actual `run_attempt` entry body with zero headers is terminal.

This composes the real entry prefix (`pl = load(si + 0)` then the skip, which reaches the header call
site `runAttemptAt 2` in zero ticks) with the checked zero-header caller terminal
(`validate_headers` zero body, the count reload and the empty-header guard).  Nothing about nonzero
headers, a selected parent, a header table or a witness array is assumed: only the typed `si`, the
locally declared `pl`, the typed record cells `si+0`/`si+72`/`si+80`, the typed live heap and the
original code.

Outcome reading.  `StAbort` is a property of **all** non-returning runs: it says the result is not a
`returned` value, the clock is not exceeded, and the run never times out.  In the zero-header path the
run may therefore stop through an allocator failure inside the header body, through any other source
error, or through the empty-header guard.  Only when the header call itself returns normally is the
abort site forced to be the guard, and then the failure is exactly `BlockErr 3`
(`run_attempt_zero_header_guard_aborts`).
-/
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
set_option maxRecDepth 100000
set_option maxHeartbeats 800000

/-- **The actual `run_attempt` entry body with zero headers never returns.**  From the real function
body `runAttemptAt 0`, with the typed `si`, its first record word `si+0` holding the decoded payload,
the typed record cells `si+72`/`si+80` holding the header pointer and the zero header count, the typed
capped live heap and the original code, the run declares `pl`, calls the real `validate_headers` on the
empty array, reloads the preserved zero count and raises `BlockErr 3`: the whole entry prefix is a
non-returning run within eight source ticks, so the parent load at `runAttemptAt 5` is never reached.

`StAbort` deliberately covers every non-returning outcome (allocator failure, any source error, and
the guard's `BlockErr 3`); the guard is the only abort site reachable when the header call returns, and
that case is `run_attempt_zero_header_guard_aborts`. -/
theorem run_attempt_zero_header_entry_terminal {F : Type} (s : PanSemStateFiniteExact 64 F)
    (si payload headers heap : BitVec 64) (code : s.code = originalRuntimeCode)
    (atSi : s.locals.lookup (ofString "si") = some (.val (.word si)))
    (siDomain : s.memaddrs (si + (0#64)))
    (siCell : s.memory (si + (0#64)) = .word payload)
    (pointerDomain : s.memaddrs (si + (72#64)))
    (pointerCell : s.memory (si + (72#64)) = .word headers)
    (countDomain : s.memaddrs (si + (80#64)))
    (countCell : s.memory (si + (80#64)) = .word (0 : BitVec 64))
    (heapGlobal : s.globals.lookup (ofString "heap_ptr") = some (.val (.word heap)))
    (capped : heap.toNat ≤ 33806089496) (budget : 8 ≤ s.clock) :
    StAbort s (evaluateHOLFiniteState s (runAttemptAt 0)) 8 := by
  rcases run_attempt_initial_reaches s si payload atSi siDomain siCell with
    ⟨ready,facts,clockLow,clockHigh,agreement⟩ | aborted
  · obtain ⟨localsEq,atPl,memoryEq,globalsEq,memaddrsEq,codeEq⟩ := facts
    have atSiNext : ready.locals.lookup (ofString "si") = some (.val (.word si)) := by
      rw [localsEq]
      simp (config := {decide := true}) [HolFiniteMapExact.lookup_update,FUPDATE,atSi]
    have inner := run_attempt_zero_header_caller_terminal ready si headers heap
      (by rw [codeEq]; exact code) atSiNext
      (by rw [memaddrsEq]; exact pointerDomain) (by rw [memoryEq]; exact pointerCell)
      (by rw [memaddrsEq]; exact countDomain) (by rw [memoryEq]; exact countCell)
      (by rw [globalsEq]; exact heapGlobal) capped (by omega)
    obtain ⟨x,result,notReturned,low,high,noTimeout⟩ := inner
    have readyClock : ready.clock = s.clock := by omega
    rw [readyClock] at low high noTimeout
    unfold StAbort
    rw [agreement.2.1]
    exact ⟨x, agreement.1.trans result, notReturned, low, high, noTimeout⟩
  · exact stAbort_mono s _ 0 8 (by omega) aborted


/-- The same entry run as a plain all-outcome tick bound: it never times out and spends at most eight
source ticks, whatever the outcome. -/
theorem run_attempt_zero_header_entry_runBounded {F : Type} (s : PanSemStateFiniteExact 64 F)
    (si payload headers heap : BitVec 64) (code : s.code = originalRuntimeCode)
    (atSi : s.locals.lookup (ofString "si") = some (.val (.word si)))
    (siDomain : s.memaddrs (si + (0#64)))
    (siCell : s.memory (si + (0#64)) = .word payload)
    (pointerDomain : s.memaddrs (si + (72#64)))
    (pointerCell : s.memory (si + (72#64)) = .word headers)
    (countDomain : s.memaddrs (si + (80#64)))
    (countCell : s.memory (si + (80#64)) = .word (0 : BitVec 64))
    (heapGlobal : s.globals.lookup (ofString "heap_ptr") = some (.val (.word heap)))
    (capped : heap.toNat ≤ 33806089496) (budget : 8 ≤ s.clock) :
    RunBounded s (runAttemptAt 0) 8 := by
  obtain ⟨x,result,notReturned,low,high,noTimeout⟩ :=
    run_attempt_zero_header_entry_terminal s si payload headers heap code atSi siDomain siCell
      pointerDomain pointerCell countDomain countCell heapGlobal capped budget
  refine ⟨low,high,?_⟩
  rw [result]
  exact fun same => noTimeout budget (Option.some.inj same)


/-- The same entry terminal stated on the decoder's own link contract: the witness array read from
`si+72` holds the header pointer and the count read from `si+80` is zero.  This is the shape a
decoder contract hands over, so no raw cell facts are needed. -/
theorem run_attempt_zero_header_entry_terminal_linked {F : Type} (s : PanSemStateFiniteExact 64 F)
    (si payload array count input inputLength heap : BitVec 64) (code : s.code = originalRuntimeCode)
    (atSi : s.locals.lookup (ofString "si") = some (.val (.word si)))
    (siDomain : s.memaddrs (si + (0#64)))
    (siCell : s.memory (si + (0#64)) = .word payload)
    (linked : WitnessArrayLinked s si 72 80 array count input inputLength heap)
    (zero : count = 0)
    (heapGlobal : s.globals.lookup (ofString "heap_ptr") = some (.val (.word heap)))
    (capped : heap.toNat ≤ 33806089496) (budget : 8 ≤ s.clock) :
    StAbort s (evaluateHOLFiniteState s (runAttemptAt 0)) 8 := by
  subst zero
  exact run_attempt_zero_header_entry_terminal s si payload array heap code atSi siDomain siCell
    linked.pointerDomain linked.pointerCell linked.countDomain linked.countCell heapGlobal capped budget

#print axioms run_attempt_zero_header_entry_terminal_linked

#print axioms run_attempt_zero_header_entry_runBounded

#print axioms run_attempt_zero_header_entry_terminal
end InitECandidate.Runtime
