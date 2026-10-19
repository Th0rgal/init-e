import InitECandidate.Runtime.ValidateHeadersSecondPhaseBound
import InitECandidate.Runtime.HtabSetBound
import InitECandidate.Runtime.MemeqReadFrame
import InitECandidate.Runtime.OriginalMemeqCode
import InitECandidate.Runtime.AvoidsLocalFrame
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
set_option maxRecDepth 40000
set_option maxHeartbeats 2000000

/-! ### Memory and globals never change in the `At 5` phase -/

theorem validateHeadersSecondGuard_memoryFrame : MemoryFrame validateHeadersSecondGuard := by
  rw [validateHeadersSecondGuard]
  exact memoryFrame_ite (.cmp .equal (.var .local (ofString "eq")) (.const 0))
    (yes := .raise (ofString "BlockErr") (.const 2)) (no := .skip)
    (memoryFrame_leaf _ (by decide)) (memoryFrame_leaf _ (by decide))

theorem validateHeadersSecondContinuation_memoryFrame : MemoryFrame validateHeadersSecondContinuation := by
  rw [validateHeadersSecondContinuation]
  exact memoryFrame_seq (first := validateHeadersSecondGuard)
    (second := .assign .local (ofString "i") (.op .add [.var .local (ofString "i"), .const 1]))
    validateHeadersSecondGuard_memoryFrame (memoryFrame_leaf _ (by decide))

theorem validateHeadersSecondBody_memoryFrame : MemoryFrame validateHeadersSecondBody := by
  rw [source_validate_headers_second_body_split]
  exact memoryFrame_decCall (ofString "eq") (ofString "memeq") .one validateHeadersSecondArguments
    (continuation := validateHeadersSecondContinuation) _ _ _ originalRuntimeCode_memeq_lookup
    (memoryFrame_leaf _ memeq_readOnlyMemory) validateHeadersSecondContinuation_memoryFrame

theorem validateHeadersSecondLoop_memoryFrame : MemoryFrame validateHeadersSecondLoop := by
  rw [validateHeadersSecondLoop]
  exact memoryFrame_while validateHeadersSecondCondition validateHeadersSecondBody_memoryFrame

theorem validateHeadersSecondTail_memoryFrame : MemoryFrame validateHeadersSecondTail := by
  rw [validateHeadersSecondTail]
  exact memoryFrame_seq (first := validateHeadersSecondLoop) (second := validateHeadersSecondReturn)
    validateHeadersSecondLoop_memoryFrame (memoryFrame_leaf _ (by decide))

theorem validateHeadersSecondPhase_memoryFrame : MemoryFrame (validateHeadersSecondAt 5) := by
  rw [source_validate_headers_second_phase]
  exact memoryFrame_seq (first := .assign .local (ofString "i") (.const 1)) (second := validateHeadersSecondTail)
    (memoryFrame_leaf _ (by decide)) validateHeadersSecondTail_memoryFrame

/-- Every outcome of the actual `At 5` phase keeps the whole memory, the
globals, the address domain, the endianness marker and the code: the `memeq`
call is read-only and nothing else in the phase stores, allocates or rebinds
code. -/
theorem evaluate_validate_headers_second_phase_frame {F : Type} (s : PanSemStateFiniteExact 64 F)
    (code : s.code = originalRuntimeCode) :
    (evaluateHOLFiniteState s (validateHeadersSecondAt 5)).2.memory = s.memory ∧
      (evaluateHOLFiniteState s (validateHeadersSecondAt 5)).2.globals = s.globals ∧
      (evaluateHOLFiniteState s (validateHeadersSecondAt 5)).2.memaddrs = s.memaddrs ∧
      (evaluateHOLFiniteState s (validateHeadersSecondAt 5)).2.be = s.be ∧
      (evaluateHOLFiniteState s (validateHeadersSecondAt 5)).2.code = s.code := by
  have memory := validateHeadersSecondPhase_memoryFrame s code
  have metadata := evaluateHOLFiniteState_metadata s (validateHeadersSecondAt 5)
  exact ⟨memory.1,memory.2,metadata.2.1,metadata.2.2.1,metadata.1⟩

/-! ### The phase returns exactly the `(hs, hashes)` pair -/

/-- The `eq = 0` guard never finishes with a top-level `return`. -/
theorem validateHeadersSecondGuard_noReturn {F : Type} (s : PanSemStateFiniteExact 64 F)
    (v : ValueHOL 64) :
    (evaluateHOLFiniteState s validateHeadersSecondGuard).1 ≠ some (.returned v) := by
  rw [validateHeadersSecondGuard,evaluateHOLFiniteState_ite]
  split
  · split
    · simp
    · rw [evaluateHOLFiniteState_raise]
      repeat' first | split | simp
  · simp

/-- The guard plus the real increment never finishes with a top-level `return`. -/
theorem validateHeadersSecondContinuation_noReturn {F : Type} (s : PanSemStateFiniteExact 64 F)
    (v : ValueHOL 64) :
    (evaluateHOLFiniteState s validateHeadersSecondContinuation).1 ≠ some (.returned v) := by
  rw [validateHeadersSecondContinuation,evaluateHOLFiniteState_seq_line780]
  cases guardRun : evaluateHOLFiniteState s validateHeadersSecondGuard with
  | mk r start =>
    dsimp only
    cases r with
    | none =>
      rw [evaluateHOLFiniteState_assign]
      repeat' first | split | simp
    | some r' =>
      have never := validateHeadersSecondGuard_noReturn s v
      rw [guardRun] at never
      exact never

/-- The real loop body never finishes with a top-level `return`: `memeq`
returns into its continuation and nothing else returns. -/
theorem validateHeadersSecondBody_noReturn {F : Type} (s : PanSemStateFiniteExact 64 F)
    (v : ValueHOL 64) :
    (evaluateHOLFiniteState s validateHeadersSecondBody).1 ≠ some (.returned v) := by
  intro hret
  have full : evaluateHOLFiniteState s validateHeadersSecondBody =
      (some (.returned v),(evaluateHOLFiniteState s validateHeadersSecondBody).2) := Prod.ext hret rfl
  rw [source_validate_headers_second_body_split] at full
  obtain ⟨values,body,callee,returnShape,w,bodyPost,resumed,inner,_,_,_,_,_,_,_,_,_,_,contRun,_⟩ :=
    decCall_returned_body full
  exact validateHeadersSecondContinuation_noReturn resumed v (by rw [contRun])

/-- A `while` whose body never finishes with a top-level `return` never does
either. -/
theorem evaluate_while_noReturn (condition : ExpHOL 64) (body : ProgHOL 64)
    (never : ∀ {F : Type} (s : PanSemStateFiniteExact 64 F) (v : ValueHOL 64),
      (evaluateHOLFiniteState s body).1 ≠ some (.returned v)) :
    ∀ n : Nat, ∀ {F : Type} (s : PanSemStateFiniteExact 64 F) (v : ValueHOL 64), s.clock = n →
      (evaluateHOLFiniteState s (.while condition body)).1 ≠ some (.returned v) := by
  intro n
  induction n using Nat.strongRecOn with
  | ind n ih =>
    intro F s v clock
    rw [evaluateHOLFiniteState_while_total]
    split
    · split
      · split
        · simp
        · dsimp only
          rw [fixClockHOLFinite_evaluateState]
          cases run : evaluateHOLFiniteState (decClockHOLFinite s) body with
          | mk r mid =>
            have remaining := evaluateHOLFiniteState_clock_le (decClockHOLFinite s) body
            rw [run] at remaining
            have smaller : mid.clock < n := by
              change mid.clock ≤ s.clock - 1 at remaining
              omega
            cases r with
            | none =>
              apply ih
              · exact smaller
              · rfl
            | some r' =>
              cases r' with
              | «continue» =>
                apply ih
                · exact smaller
                · rfl
              | returned u =>
                intro hret
                exact never (decClockHOLFinite s) u (by rw [run])
              | _ => simp
      · simp
    · simp

/-- The real second loop never finishes with a top-level `return`. -/
theorem validateHeadersSecondLoop_noReturn {F : Type} (s : PanSemStateFiniteExact 64 F)
    (v : ValueHOL 64) :
    (evaluateHOLFiniteState s validateHeadersSecondLoop).1 ≠ some (.returned v) :=
  evaluate_while_noReturn validateHeadersSecondCondition validateHeadersSecondBody
    validateHeadersSecondBody_noReturn s.clock s v rfl

/-- On every `returned` outcome of the actual `At 5` phase the value is the
real `(hs, hashes)` pair built from the entry locals, and the whole memory,
globals, address domain, endianness marker and code survive. -/
theorem evaluate_validate_headers_second_phase_returned {F : Type} (s : PanSemStateFiniteExact 64 F)
    (hs hashes : BitVec 64) (v : ValueHOL 64) (post : PanSemStateFiniteExact 64 F)
    (code : s.code = originalRuntimeCode)
    (atHs : s.locals.lookup (ofString "hs") = some (.val (.word hs)))
    (atHashes : s.locals.lookup (ofString "hashes") = some (.val (.word hashes)))
    (run : evaluateHOLFiniteState s (validateHeadersSecondAt 5) = (some (.returned v),post)) :
    v = .rStruct [.val (.word hs),.val (.word hashes)] ∧
      post.memory = s.memory ∧ post.globals = s.globals ∧ post.memaddrs = s.memaddrs ∧
      post.be = s.be ∧ post.code = s.code := by
  have frame := evaluate_validate_headers_second_phase_frame s code
  rw [run] at frame
  refine ⟨?_,frame⟩
  rw [source_validate_headers_second_phase,evaluateHOLFiniteState_seq_line780] at run
  cases resetRun : evaluateHOLFiniteState s (.assign .local (ofString "i") (.const 1)) with
  | mk r start =>
    rw [resetRun] at run
    dsimp only at run
    cases r with
    | some r' =>
      dsimp only at run
      rw [evaluateHOLFiniteState_assign] at resetRun
      repeat' first | split at resetRun | simp at resetRun
      all_goals
        have rReturned : r' = .returned v := Option.some.inj (Prod.mk.inj run).1
        obtain ⟨rEq,_⟩ := resetRun
        rw [rReturned] at rEq
        cases rEq
    | none =>
      rw [evaluateHOLFiniteState_seq_line780] at run
      cases loopRun : evaluateHOLFiniteState start
        (.while validateHeadersSecondCondition validateHeadersSecondBody) with
      | mk r' mid =>
        rw [loopRun] at run
        dsimp only at run
        cases r' with
        | none =>
          dsimp only at run
          rw [validateHeadersSecondReturn] at run
          rw [evaluateHOLFiniteState_return] at run
          split at run
          · simp at run
          · rename_i value evalValue
            split at run
            · obtain ⟨valueEq,_⟩ := Prod.mk.inj run
              have resetHs : start.locals.lookup (ofString "hs") = some (.val (.word hs)) := by
                have flowing := evaluate_avoidsLocal_flowing (ofString "hs")
                  (.assign .local (ofString "i") (.const 1)) (by decide) s (Or.inl (by rw [resetRun]))
                rw [resetRun] at flowing
                dsimp only at flowing
                exact flowing.trans atHs
              have resetHashes : start.locals.lookup (ofString "hashes") = some (.val (.word hashes)) := by
                have flowing := evaluate_avoidsLocal_flowing (ofString "hashes")
                  (.assign .local (ofString "i") (.const 1)) (by decide) s (Or.inl (by rw [resetRun]))
                rw [resetRun] at flowing
                dsimp only at flowing
                exact flowing.trans atHashes
              have loopHs : mid.locals.lookup (ofString "hs") = some (.val (.word hs)) := by
                have flowing := evaluate_avoidsLocal_flowing (ofString "hs")
                  (.while validateHeadersSecondCondition validateHeadersSecondBody) (by decide) start
                  (Or.inl (by rw [loopRun]))
                rw [loopRun] at flowing
                dsimp only at flowing
                exact flowing.trans resetHs
              have loopHashes : mid.locals.lookup (ofString "hashes") = some (.val (.word hashes)) := by
                have flowing := evaluate_avoidsLocal_flowing (ofString "hashes")
                  (.while validateHeadersSecondCondition validateHeadersSecondBody) (by decide) start
                  (Or.inl (by rw [loopRun]))
                rw [loopRun] at flowing
                dsimp only at flowing
                exact flowing.trans resetHashes
              have evaluateStruct : @evalHOLExact 64 F _ mid.toExact
                  (fun address => Classical.propDecidable (mid.toExact.memaddrs address))
                  (.rstruct [.var .local (ofString "hs"),.var .local (ofString "hashes")]) =
                  some (ValueHOL.rStruct [ValueHOL.val (HolWordLab.word hs),ValueHOL.val (HolWordLab.word hashes)]) := by
                simp [evalHOLExact,evalListHOLExact,loopHs,loopHashes]
              rw [evaluateStruct] at evalValue
              have valueIs : value = .rStruct [.val (.word hs),.val (.word hashes)] :=
                (Option.some.inj evalValue).symm
              have valueIsV : value = v := PanSemResultExact.returned.inj (Option.some.inj valueEq)
              exact valueIsV.symm.trans valueIs
            · simp at run
        | some r'' =>
          obtain ⟨loopEq,_⟩ := Prod.mk.inj run
          rw [loopEq] at loopRun
          exfalso
          exact (evaluate_while_noReturn validateHeadersSecondCondition validateHeadersSecondBody
            validateHeadersSecondBody_noReturn start.clock start v rfl) (by rw [loopRun])

#print axioms validateHeadersSecondGuard_memoryFrame
#print axioms validateHeadersSecondContinuation_memoryFrame
#print axioms validateHeadersSecondBody_memoryFrame
#print axioms validateHeadersSecondLoop_memoryFrame
#print axioms validateHeadersSecondTail_memoryFrame
#print axioms validateHeadersSecondPhase_memoryFrame
#print axioms evaluate_validate_headers_second_phase_frame
#print axioms validateHeadersSecondGuard_noReturn
#print axioms validateHeadersSecondContinuation_noReturn
#print axioms validateHeadersSecondBody_noReturn
#print axioms evaluate_while_noReturn
#print axioms validateHeadersSecondLoop_noReturn
#print axioms evaluate_validate_headers_second_phase_returned
end InitECandidate.Runtime

