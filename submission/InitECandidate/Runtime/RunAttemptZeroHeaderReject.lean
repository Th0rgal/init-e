import InitECandidate.Runtime.RunAttemptHeadersSource
import InitECandidate.Runtime.RunAttemptHeadersEntry
import InitECandidate.Runtime.BoundedDecCallReach
import InitECandidate.Runtime.ValidateHeadersZeroBody
import InitECandidate.Runtime.RunAttemptHeaderCountReach
/-!
The actual zero-header early reject.

A canonically decoded empty header array gives header count `0`, so the main header-bound table
premise is unavailable and this path must be proved directly from the typed record cells and the
typed capped heap.  This module proves the whole caller prefix `runAttemptAt 2`: the real declaration
call of `validate_headers`, the actual count reload and the empty-header guard terminate in
`BlockErr 3` before the parent load at `runAttemptAt 5`, within eight source ticks.
-/
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
set_option maxRecDepth 100000
set_option maxHeartbeats 800000

/-- A `return` never rewrites memory: it only reports the value. -/
theorem return_memory_frame {F : Type} (s : PanSemStateFiniteExact 64 F) (expression : ExpHOL 64) :
    (evaluateHOLFiniteState s (.return expression)).2.memory = s.memory := by
  rw [evaluateHOLFiniteState_return]
  split
  · simp
  · split <;> simp [emptyLocalsHOLFinite]

/-- A `return` never rewrites the memory domain. -/
theorem return_memaddrs_frame {F : Type} (s : PanSemStateFiniteExact 64 F) (expression : ExpHOL 64) :
    (evaluateHOLFiniteState s (.return expression)).2.memaddrs = s.memaddrs := by
  rw [evaluateHOLFiniteState_return]
  split
  · simp
  · split <;> simp [emptyLocalsHOLFinite]

/-- With no headers both real loops are skipped, so the returned suffix leaves memory and the
memory domain untouched: only local variables are assigned. -/
theorem evaluate_validate_headers_zero_suffix_frame {F : Type} (s : PanSemStateFiniteExact 64 F)
    (hs hashes : BitVec 64)
    (atCount : s.locals.lookup (ofString "n") = some (.val (.word (0 : BitVec 64))))
    (atHs : s.locals.lookup (ofString "hs") = some (.val (.word hs)))
    (atHashes : s.locals.lookup (ofString "hashes") = some (.val (.word hashes))) :
    (evaluateHOLFiniteState s (validateHeadersAt 3)).2.memory = s.memory ∧
      (evaluateHOLFiniteState s (validateHeadersAt 3)).2.memaddrs = s.memaddrs := by
  let ready := setVarHOLFinite (ofString "i") (.val (.word (0 : BitVec 64))) s
  let reset := setVarHOLFinite (ofString "i") (.val (.word (1 : BitVec 64))) ready
  have firstCondition : evalHOLFinite ready (h := fun a => Classical.propDecidable (ready.memaddrs a)) validateHeadersFirstCondition = some (.val (.word (0 : BitVec 64))) := by
    rw [evalHOLFinite_eq_toExact]
    simp (config := {decide := true}) [ready,validateHeadersFirstCondition,evalHOLExact,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,
      atCount,Compiler.Encoders.Asm.wordCmpHOL,Compiler.Encoders.Asm.holAsmSignedLess]
  have secondCondition : evalHOLFinite reset (h := fun a => Classical.propDecidable (reset.memaddrs a)) validateHeadersSecondCondition = some (.val (.word (0 : BitVec 64))) := by
    rw [evalHOLFinite_eq_toExact]
    simp (config := {decide := true}) [reset,ready,validateHeadersSecondCondition,evalHOLExact,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,
      atCount,Compiler.Encoders.Asm.wordCmpHOL,Compiler.Encoders.Asm.holAsmSignedLess]
  have firstSkip : evaluateHOLFiniteState ready (.while validateHeadersFirstCondition validateHeadersFirstBody) = (none,ready) := by
    rw [evaluateHOLFiniteState_while_total,firstCondition]
    simp
  have secondSkip : evaluateHOLFiniteState reset validateHeadersSecondLoop = (none,reset) := by
    rw [validateHeadersSecondLoop,evaluateHOLFiniteState_while_total,secondCondition]
    simp
  have assigned : evaluateHOLFiniteState ready (.assign .local (ofString "i") (.const 1)) = (none,reset) := by
    simp [evaluateHOLFiniteState_assign,evalHOLExact,lookupKvarHOLFinite,ready,reset,setKvarHOLFinite,
      setVarHOLFinite,isValidValueHOLFinite,shapeOfHOLExact,shapeEqHOL,HolFiniteMapExact.lookup_update,FUPDATE]
  rw [source_validate_headers_index_init,evaluateHOLFiniteState_dec_total]
  simp only [evalHOLExact,shapeOfHOLExact,shapeEqHOL,if_true]
  change (evaluateHOLFiniteState ready (validateHeadersAt 4)).2.memory = s.memory ∧
    (evaluateHOLFiniteState ready (validateHeadersAt 4)).2.memaddrs = s.memaddrs
  rw [source_validate_headers_first_loop,evaluateHOLFiniteState_seq_line780,firstSkip]
  dsimp only
  rw [show validateHeadersAt 5 = .seq (.assign .local (ofString "i") (.const 1))
      validateHeadersSecondTail from source_validate_headers_second_tail]
  rw [evaluateHOLFiniteState_seq_line780,assigned]
  dsimp only
  unfold validateHeadersSecondTail
  rw [evaluateHOLFiniteState_seq_line780,secondSkip]
  dsimp only
  unfold validateHeadersSecondReturn
  rw [return_memory_frame,return_memaddrs_frame]
  simp [ready,reset,setVarHOLFinite]

/-- **The zero-header body preserves memory and the memory domain on any returned run.**
Allocations only move the live heap pointer, both real loops are skipped, and the returned suffix
assigns locals only; an allocator failure is not a returned run and so cannot occur here. -/
theorem validate_headers_zero_body_returned_frame {F : Type} (s : PanSemStateFiniteExact 64 F)
    (heap : BitVec 64) (code : s.code = originalRuntimeCode)
    (atCount : s.locals.lookup (ofString "n") = some (.val (.word (0 : BitVec 64))))
    (heapGlobal : s.globals.lookup (ofString "heap_ptr") = some (.val (.word heap)))
    (heapBound : heap.toNat ≤ 33806089496) (budget : 4 ≤ s.clock)
    (value : ValueHOL 64) (post : PanSemStateFiniteExact 64 F)
    (run : evaluateHOLFiniteState s (sourceFunctionBody Guest.guestFn_validate_headers) =
      (some (.returned value),post)) :
    post.memory = s.memory ∧ post.memaddrs = s.memaddrs := by
  have allocated := validate_headers_prefix_reaches s (0 : BitVec 64) heap code atCount heapGlobal
    heapBound budget
  rw [source_validate_headers_body] at run
  rcases allocated with ⟨next,facts,_,_,agreement⟩ | aborted
  · obtain ⟨small,first,hsReady,hashesReady⟩ := facts
    have atCountNext : next.locals.lookup (ofString "n") = some (.val (.word (0 : BitVec 64))) := by
      rw [hashesReady.1,hsReady.1]
      simp (config := {decide := true}) [HolFiniteMapExact.lookup_update,FUPDATE,atCount]
    have atHsNext : next.locals.lookup (ofString "hs") = some (.val (.word heap)) := by
      rw [hashesReady.1,hsReady.1]
      simp (config := {decide := true}) [HolFiniteMapExact.lookup_update,FUPDATE]
    have atHashesNext : next.locals.lookup (ofString "hashes") =
        some (.val (.word (allocationEnd heap (validateHeadersHsSize (0 : BitVec 64))))) := by
      rw [hashesReady.1]
      simp (config := {decide := true}) [HolFiniteMapExact.lookup_update,FUPDATE]
    have suffix := evaluate_validate_headers_zero_suffix_frame next heap
      (allocationEnd heap (validateHeadersHsSize (0 : BitVec 64))) atCountNext atHsNext atHashesNext
    have memoryChain : post.memory = next.memory ∧ post.memaddrs = next.memaddrs := by
      have step : post = (evaluateHOLFiniteState s (validateHeadersAt 0)).2 :=
        (congrArg Prod.snd run).symm
      rw [step]
      exact ⟨agreement.2.2.1.trans suffix.1, agreement.2.2.2.2.trans suffix.2⟩
    rw [memoryChain.1,memoryChain.2,hashesReady.2.1,hsReady.2.1,hashesReady.2.2.2.1,hsReady.2.2.2.1]
    exact ⟨rfl,rfl⟩
  · obtain ⟨x,result,notReturned,_,_⟩ := aborted
    have returned := congrArg Prod.fst run
    rw [result] at returned
    exact (notReturned value (Option.some.inj returned)).elim

/-- The actual count reload followed by the empty-header guard, as a reach: from `runAttemptAt 3`
with the zero header count still in the typed `si+80` cell, the prefix is a terminal abort. -/
theorem reaches_run_attempt_zero_count_guard {F : Type} (s : PanSemStateFiniteExact 64 F)
    (si : BitVec 64)
    (atSi : s.locals.lookup (ofString "si") = some (.val (.word si)))
    (domain : s.memaddrs (si + (80#64)))
    (cell : s.memory (si + (80#64)) = .word (0 : BitVec 64)) :
    Reaches s (runAttemptAt 3) (fun _ => False) 0 (runAttemptAt 5) := by
  have loaded := run_attempt_header_count_reaches s si (0 : BitVec 64) atSi domain cell
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

/-- **The empty-header guard is terminal.**  At `runAttemptAt 3`, with the typed `si` record cell
`si+80` still holding the zero header count, the actual count reload binds `nh := 0` and the guard
raises `BlockErr 3`; the prefix is a terminal abort with no source tick and the parent load at
`runAttemptAt 5` is never reached. -/
theorem run_attempt_zero_header_guard_aborts {F : Type} (s : PanSemStateFiniteExact 64 F)
    (si : BitVec 64)
    (atSi : s.locals.lookup (ofString "si") = some (.val (.word si)))
    (domain : s.memaddrs (si + (80#64)))
    (cell : s.memory (si + (80#64)) = .word (0 : BitVec 64)) :
    StAbort s (evaluateHOLFiniteState s (runAttemptAt 3)) 0 := by
  rcases reaches_run_attempt_zero_count_guard s si atSi domain cell with
    ⟨next,facts,_,_,_⟩ | done
  · exact facts.elim
  · exact done

/-- **The whole zero-header caller prefix is terminal.**  From `runAttemptAt 2`, with the typed `si`,
the typed record cells `si+72`/`si+80` holding the header pointer and the zero header count, the
typed capped live heap and the original code, the actual `validate_headers` call runs its whole zero
body, the caller reloads the preserved zero count and the guard raises `BlockErr 3`: the prefix ends
in a terminal abort within eight source ticks, before the parent load at `runAttemptAt 5`.  No header
table, witness-array or parser premise is used. -/
theorem run_attempt_zero_header_caller_terminal {F : Type} (s : PanSemStateFiniteExact 64 F)
    (si headers heap : BitVec 64) (code : s.code = originalRuntimeCode)
    (atSi : s.locals.lookup (ofString "si") = some (.val (.word si)))
    (pointerDomain : s.memaddrs (si + (72#64)))
    (pointerCell : s.memory (si + (72#64)) = .word headers)
    (countDomain : s.memaddrs (si + (80#64)))
    (countCell : s.memory (si + (80#64)) = .word (0 : BitVec 64))
    (heapGlobal : s.globals.lookup (ofString "heap_ptr") = some (.val (.word heap)))
    (capped : heap.toNat ≤ 33806089496) (budget : 8 ≤ s.clock) :
    StAbort s (evaluateHOLFiniteState s (runAttemptAt 2)) 8 := by
  let P : PanSemStateFiniteExact 64 F → Prop := fun ready =>
    ready.memory (si + (80#64)) = .word (0 : BitVec 64) ∧ ready.memaddrs (si + (80#64)) ∧
      ready.locals.lookup (ofString "si") = some (.val (.word si))
  have args : evalListHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a))
      runAttemptHeadersArguments = some [.val (.word headers),.val (.word (0 : BitVec 64))] := by
    rw [evalListHOLFinite_eq_toExact]
    simp [runAttemptHeadersArguments,evalListHOLExact,evalHOLExact,atSi,wordOpHOL,wordOp,valueIsWord,valueWord,
      isWfShapeExactHOL,memLoadHOLExact,pointerDomain,countDomain,pointerCell,countCell]
  have lookup : lookupCodeHOLFinite s.code.lookup (ofString "validate_headers")
      [.val (.word headers),.val (.word (0 : BitVec 64))] =
      some (sourceFunctionBody Guest.guestFn_validate_headers,validateHeadersCallee headers (0 : BitVec 64),
        .comb [.one,.one]) := by
    rw [code]
    exact lookup_validate_headers_callee headers (0 : BitVec 64)
  have bounded : RunBounded (callEntryStateHOLFinite s (validateHeadersCallee headers (0 : BitVec 64)))
      (sourceFunctionBody Guest.guestFn_validate_headers) 4 := by
    refine runBounded_validate_headers_zero_body _ heap ?_ ?_ ?_ capped ?_
    · show s.code = originalRuntimeCode
      exact code
    · simp [callEntryStateHOLFinite,validateHeadersCallee,HolFiniteMapExact.lookup_update,FUPDATE]
    · show s.globals.lookup (ofString "heap_ptr") = some (.val (.word heap))
      exact heapGlobal
    · show 4 ≤ s.clock - 1
      omega
  have raw : Reaches s (.decCall (ofString "vh") (.comb [.one,.one]) (ofString "validate_headers")
      runAttemptHeadersArguments (runAttemptAt 3)) P 5 (runAttemptAt 3) := by
    refine bounded_decCall_reaches s (ofString "vh") (ofString "validate_headers") (.comb [.one,.one])
      (.comb [.one,.one]) runAttemptHeadersArguments [.val (.word headers),.val (.word (0 : BitVec 64))]
      (sourceFunctionBody Guest.guestFn_validate_headers) (runAttemptAt 3)
      (validateHeadersCallee headers (0 : BitVec 64)) 4 P args lookup (by omega) bounded ?_
    intro value post bodyRun shapes
    have frame := validate_headers_zero_body_returned_frame
      (callEntryStateHOLFinite s (validateHeadersCallee headers (0 : BitVec 64))) heap
      (by show s.code = originalRuntimeCode; exact code)
      (by simp [callEntryStateHOLFinite,validateHeadersCallee,HolFiniteMapExact.lookup_update,FUPDATE])
      (by show s.globals.lookup (ofString "heap_ptr") = some (.val (.word heap)); exact heapGlobal)
      capped (by show 4 ≤ s.clock - 1; omega) value post bodyRun
    refine ⟨?_,?_,?_⟩
    · show post.memory (si + (80#64)) = .word (0 : BitVec 64)
      rw [frame.1]
      show s.memory (si + (80#64)) = .word (0 : BitVec 64)
      exact countCell
    · show post.memaddrs (si + (80#64))
      rw [frame.2]
      exact countDomain
    · show s.locals.lookup (ofString "si") = some (.val (.word si))
      exact atSi
  have callReach : Reaches s (runAttemptAt 2) P 5 (runAttemptAt 3) :=
    source_run_attempt_headers_call ▸ raw
  have composed : Reaches s (runAttemptAt 2) (fun _ => False) (5 + 0) (runAttemptAt 5) :=
    reaches_trans s (runAttemptAt 2) (runAttemptAt 3) (runAttemptAt 5) P (fun _ => False) 5 0 callReach
      (fun next facts => reaches_run_attempt_zero_count_guard next si facts.2.2 facts.2.1 facts.1)
  rcases composed with ⟨next,facts,_,_,_⟩ | done
  · exact facts.elim
  · exact stAbort_mono s _ 5 8 (by omega) done

#print axioms return_memory_frame
#print axioms return_memaddrs_frame
#print axioms evaluate_validate_headers_zero_suffix_frame
#print axioms validate_headers_zero_body_returned_frame
#print axioms reaches_run_attempt_zero_count_guard
#print axioms run_attempt_zero_header_guard_aborts
#print axioms run_attempt_zero_header_caller_terminal
end InitECandidate.Runtime
