import InitECandidate.Runtime.RunAttemptParentReach
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- The real count reload, empty-list exception guard and parent declaration
compose without a source clock tick. The parent comes from the initialized
pointer buffer, rather than an assumed individual cell value. -/
theorem run_attempt_count_parent_reaches {F : Type} (s : PanSemStateFiniteExact 64 F)
    (si headers hashes count : BitVec 64)
    (atSi : s.locals.lookup (ofString "si") = some (.val (.word si)))
    (atHeaders : s.locals.lookup (ofString "vh") =
      some (.rStruct [.val (.word headers),.val (.word hashes)]))
    (countDomain : s.memaddrs (si + (80#64)))
    (countCell : s.memory (si + (80#64)) = .word count)
    (initialized : HeaderPointerPrefix s headers count.toNat) :
    Reaches s (runAttemptAt 3)
      (fun ready => count ≠ 0 ∧ ∃ parent : BitVec 64,
        ready = setVarHOLFinite (ofString "parent") (.val (.word parent))
          (setVarHOLFinite (ofString "nh") (.val (.word count)) s))
      0 (runAttemptAt 6) := by
  have prefixRun := run_attempt_header_count_and_guard_reaches s si count atSi countDomain countCell
  have combined := reaches_trans s (runAttemptAt 3) (runAttemptAt 5) (runAttemptAt 6)
    (fun next => next = setVarHOLFinite (ofString "nh") (.val (.word count)) s ∧ count ≠ 0)
    (fun ready => count ≠ 0 ∧ ∃ parent : BitVec 64,
      ready = setVarHOLFinite (ofString "parent") (.val (.word parent))
        (setVarHOLFinite (ofString "nh") (.val (.word count)) s)) 0 0 prefixRun (by
      intro next facts
      obtain ⟨same,nonzero⟩ := facts
      subst next
      have vh : (setVarHOLFinite (ofString "nh") (.val (.word count)) s).locals.lookup
          (ofString "vh") = some (.rStruct [.val (.word headers),.val (.word hashes)]) := by
        simpa (config := {decide := true}) [setVarHOLFinite,FUPDATE] using atHeaders
      have nh : (setVarHOLFinite (ofString "nh") (.val (.word count)) s).locals.lookup
          (ofString "nh") = some (.val (.word count)) := by simp [setVarHOLFinite,FUPDATE]
      have initializedNext := initialized.after_frame s
        (setVarHOLFinite (ofString "nh") (.val (.word count)) s) headers count.toNat rfl (fun _ _ => rfl)
      obtain ⟨parent,parentRun⟩ := run_attempt_parent_prefix_reaches _ headers hashes count vh nh initializedNext nonzero
      exact reaches_mono _ (runAttemptAt 5) (runAttemptAt 6) _ _ 0 0 (le_refl _)
        (fun ready same => ⟨nonzero,parent,same⟩) parentRun)
  exact combined

#print axioms run_attempt_count_parent_reaches

/-- The validation contract's retained record window and initialized buffer
are sufficient for the actual caller prefix through the parent declaration. -/
theorem run_attempt_count_parent_window_reaches {F : Type}
    (before ready : PanSemStateFiniteExact 64 F)
    (si array count input length heap hashes : BitVec 64) (ceiling : Nat)
    (linked : WitnessArrayLinked before si 72 80 array count input length heap)
    (atSi : ready.locals.lookup (ofString "si") = some (.val (.word si)))
    (atHeaders : ready.locals.lookup (ofString "vh") =
      some (.rStruct [.val (.word heap),.val (.word hashes)]))
    (domain : ready.memaddrs = before.memaddrs)
    (recordAbove : ceiling ≤ si.toNat)
    (recordBefore : si.toNat + 88 ≤ heap.toNat)
    (window : ∀ address : BitVec 64, ceiling ≤ address.toNat → address.toNat < heap.toNat →
      ready.memory address = before.memory address)
    (initialized : HeaderPointerPrefix ready heap count.toNat) :
    Reaches ready (runAttemptAt 3)
      (fun next => count ≠ 0 ∧ ∃ parent : BitVec 64,
        next = setVarHOLFinite (ofString "parent") (.val (.word parent))
          (setVarHOLFinite (ofString "nh") (.val (.word count)) ready))
      0 (runAttemptAt 6) := by
  have cellAddress : (si + (80#64)).toNat = si.toNat + 80 := by
    have top := heap.isLt
    rw [BitVec.toNat_add]
    change (si.toNat + 80) % 2^64 = si.toNat + 80
    exact Nat.mod_eq_of_lt (by omega)
  apply run_attempt_count_parent_reaches ready si heap hashes count atSi atHeaders
  · rw [domain]
    exact linked.countDomain
  · rw [window _ (by rw [cellAddress]; omega) (by rw [cellAddress]; omega)]
    exact linked.countCell
  · exact initialized

#print axioms run_attempt_count_parent_window_reaches
end InitECandidate.Runtime
