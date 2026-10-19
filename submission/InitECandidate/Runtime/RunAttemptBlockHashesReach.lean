import InitECandidate.Runtime.RunAttemptCountParentReach
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

theorem global_word_assignment_reaches {F : Type} (s : PanSemStateFiniteExact 64 F)
    (name : MlS) (expression : ExpHOL 64) (word : BitVec 64) (rest : ProgHOL 64)
    (value : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) expression =
      some (.val (.word word))) :
    Reaches s (.seq (.assign .global name expression) rest)
      (fun next => next = setGlobalHOLFinite name (.val (.word word)) s) 0 rest := by
  apply reaches_seq
  rw [evaluateHOLFiniteState_assign,value]
  dsimp only
  split
  · left
    exact ⟨_,rfl,by simp [setKvarHOLFinite,setGlobalHOLFinite],by simp [setKvarHOLFinite,setGlobalHOLFinite],rfl⟩
  · right
    exact stAbort_error s 0

theorem source_run_attempt_block_hashes : runAttemptAt 6 =
    .seq (.assign .global (ofString "block_hashes") (.rfield 1 (.var .local (ofString "vh"))))
      (runAttemptAt 7) := rfl

theorem source_run_attempt_block_hashes_count : runAttemptAt 7 =
    .seq (.assign .global (ofString "block_hashes_n") (.var .local (ofString "nh")))
      (runAttemptAt 8) := rfl

theorem source_run_attempt_database_skip : runAttemptAt 8 = .seq .skip (runAttemptAt 9) := rfl

/-- The actual block-hash global assignments reach the database build site
with their exact updates, or fail on an invalid global shape. Neither path
consumes a source clock tick. No prior global-shape assumption is needed. -/
theorem run_attempt_block_hashes_reaches {F : Type} (s : PanSemStateFiniteExact 64 F)
    (headers hashes count : BitVec 64)
    (atHeaders : s.locals.lookup (ofString "vh") =
      some (.rStruct [.val (.word headers),.val (.word hashes)]))
    (atCount : s.locals.lookup (ofString "nh") = some (.val (.word count))) :
    Reaches s (runAttemptAt 6)
      (fun ready => ready = setGlobalHOLFinite (ofString "block_hashes_n") (.val (.word count))
        (setGlobalHOLFinite (ofString "block_hashes") (.val (.word hashes)) s))
      0 (runAttemptAt 9) := by
  have first : Reaches s (runAttemptAt 6)
      (fun next => next = setGlobalHOLFinite (ofString "block_hashes") (.val (.word hashes)) s)
      0 (runAttemptAt 7) := by
    rw [source_run_attempt_block_hashes]
    exact global_word_assignment_reaches s _ _ hashes _ (by simp [evalHOLExact,atHeaders])
  have combined := reaches_trans s (runAttemptAt 6) (runAttemptAt 7) (runAttemptAt 9)
    _ (fun ready => ready = setGlobalHOLFinite (ofString "block_hashes_n") (.val (.word count))
      (setGlobalHOLFinite (ofString "block_hashes") (.val (.word hashes)) s)) 0 0 first (by
      intro next same
      subst next
      rw [source_run_attempt_block_hashes_count]
      have second := global_word_assignment_reaches
        (setGlobalHOLFinite (ofString "block_hashes") (.val (.word hashes)) s)
        (ofString "block_hashes_n") (.var .local (ofString "nh")) count (runAttemptAt 8)
        (by simpa [evalHOLExact,setGlobalHOLFinite] using atCount)
      exact reaches_trans _ _ (runAttemptAt 8) (runAttemptAt 9) _ _ 0 0 second (by
        intro final same
        subst final
        rw [source_run_attempt_database_skip]
        apply reaches_seq
        exact Or.inl ⟨_,rfl,by omega,le_refl _,evaluateHOLFiniteState_skip _⟩))
  exact combined

#print axioms global_word_assignment_reaches
#print axioms source_run_attempt_block_hashes
#print axioms source_run_attempt_block_hashes_count
#print axioms source_run_attempt_database_skip
#print axioms run_attempt_block_hashes_reaches
end InitECandidate.Runtime
