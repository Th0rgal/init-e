import InitECandidate.Runtime.RunAttemptHeaderCountReach
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- The caller's actual count reload and guard can use the validation
contract's older-memory window. The old linked witness supplies the original
count cell and domain; no post-call cell value is assumed. -/
theorem run_attempt_header_count_window_reaches {F : Type}
    (before ready : PanSemStateFiniteExact 64 F)
    (si array count input length heap : BitVec 64) (ceiling : Nat)
    (linked : WitnessArrayLinked before si 72 80 array count input length heap)
    (atSi : ready.locals.lookup (ofString "si") = some (.val (.word si)))
    (domain : ready.memaddrs = before.memaddrs)
    (above : ceiling ≤ (si + (80#64)).toNat)
    (below : (si + (80#64)).toNat < heap.toNat)
    (window : ∀ address : BitVec 64, ceiling ≤ address.toNat → address.toNat < heap.toNat →
      ready.memory address = before.memory address) :
    Reaches ready (runAttemptAt 3)
      (fun next => next = setVarHOLFinite (ofString "nh") (.val (.word count)) ready ∧ count ≠ 0)
      0 (runAttemptAt 5) := by
  apply run_attempt_header_count_and_guard_reaches ready si count atSi
  · rw [domain]
    exact linked.countDomain
  · rw [window _ above below]
    exact linked.countCell

/-- The validation declaration only updates `vh`, so it retains the typed
caller `si` local needed by the following source load. -/
theorem run_attempt_si_after_vh {F : Type} (before ready : PanSemStateFiniteExact 64 F)
    (si : BitVec 64) (value : ValueHOL 64)
    (atSi : before.locals.lookup (ofString "si") = some (.val (.word si)))
    (locals : ready.locals = before.locals.update (ofString "vh",value)) :
    ready.locals.lookup (ofString "si") = some (.val (.word si)) := by
  rw [locals]
  simpa (config := {decide := true}) [HolFiniteMapExact.lookup_update,FUPDATE] using atSi

#print axioms run_attempt_header_count_window_reaches
#print axioms run_attempt_si_after_vh

/-- A retained complete 88-byte stateless-input record discharges the count
cell's window bounds, without any wrapped-address premise at the call site. -/
theorem run_attempt_header_count_record_reaches {F : Type}
    (before ready : PanSemStateFiniteExact 64 F)
    (si array count input length heap : BitVec 64) (ceiling : Nat)
    (linked : WitnessArrayLinked before si 72 80 array count input length heap)
    (value : ValueHOL 64)
    (atSi : before.locals.lookup (ofString "si") = some (.val (.word si)))
    (locals : ready.locals = before.locals.update (ofString "vh",value))
    (domain : ready.memaddrs = before.memaddrs)
    (recordAbove : ceiling ≤ si.toNat)
    (recordBefore : si.toNat + 88 ≤ heap.toNat)
    (window : ∀ address : BitVec 64, ceiling ≤ address.toNat → address.toNat < heap.toNat →
      ready.memory address = before.memory address) :
    Reaches ready (runAttemptAt 3)
      (fun next => next = setVarHOLFinite (ofString "nh") (.val (.word count)) ready ∧ count ≠ 0)
      0 (runAttemptAt 5) := by
  have cellAddress : (si + (80#64)).toNat = si.toNat + 80 := by
    have top := heap.isLt
    rw [BitVec.toNat_add]
    change (si.toNat + 80) % 2^64 = si.toNat + 80
    exact Nat.mod_eq_of_lt (by omega)
  exact run_attempt_header_count_window_reaches before ready si array count input length heap ceiling
    linked (run_attempt_si_after_vh before ready si value atSi locals) domain
    (by rw [cellAddress]; omega) (by rw [cellAddress]; omega) window

#print axioms run_attempt_header_count_record_reaches
end InitECandidate.Runtime
