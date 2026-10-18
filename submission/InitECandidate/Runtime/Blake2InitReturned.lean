import InitECandidate.Runtime.Blake2InitSource
import InitECandidate.Runtime.Bn254InitReturned
import InitECandidate.Runtime.AllocationInitializersCallBound
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

/-- Globals after the first blake2_init from aligned heap H. -/
def blake2InitGlobals (g : HolFiniteMapExact MlS (ValueHOL 64)) (H : BitVec 64) : HolFiniteMapExact MlS (ValueHOL 64) :=
  (((((((g.update (ofString "heap_ptr",.val (.word (H + 80)))).update (ofString "b2_sigma",.val (.word H))).update
    (ofString "heap_ptr",.val (.word (H + 144)))).update (ofString "b2_iv",.val (.word (H + 80)))).update
    (ofString "heap_ptr",.val (.word (H + 408)))).update (ofString "b2_round",.val (.word (H + 144)))).update
    (ofString "b2_v",.val (.word (H + 152)))).update (ofString "b2_m",.val (.word (H + 280)))

theorem blake2Init_body_returned {F : Type} (state post : PanSemStateFiniteExact 64 F) (H : BitVec 64)
    (v : ValueHOL 64) (code : state.code = originalRuntimeCode)
    (heap : state.globals.lookup (ofString "heap_ptr") = some (.val (.word H)))
    (aligned : H.toNat % 8 = 0) (room : H.toNat + 512 ≤ 33806089496)
    (sigmaZero : state.globals.lookup (ofString "b2_sigma") = some (.val (.word 0)))
    (words : ∀ name ∈ [ofString "b2_iv",ofString "b2_round",ofString "b2_v",ofString "b2_m"],
      ∃ word : BitVec 64, state.globals.lookup name = some (.val (.word word)))
    (budget : 3 ≤ state.clock)
    (run : evaluateHOLFiniteState state (sourceFunctionBody Guest.guestFn_blake2_init) = (some (.returned v),post)) :
    v = .val (.word 0) ∧ post.globals = blake2InitGlobals state.globals H := by
  have q0_1 : ofString "heap_ptr" ≠ ofString "b2_sigma" := by decide
  have q0_2 : ofString "heap_ptr" ≠ ofString "b2_iv" := by decide
  have q0_3 : ofString "heap_ptr" ≠ ofString "b2_round" := by decide
  have q0_4 : ofString "heap_ptr" ≠ ofString "b2_v" := by decide
  have q0_5 : ofString "heap_ptr" ≠ ofString "b2_m" := by decide
  have q1_0 : ofString "b2_sigma" ≠ ofString "heap_ptr" := by decide
  have q1_2 : ofString "b2_sigma" ≠ ofString "b2_iv" := by decide
  have q1_3 : ofString "b2_sigma" ≠ ofString "b2_round" := by decide
  have q1_4 : ofString "b2_sigma" ≠ ofString "b2_v" := by decide
  have q1_5 : ofString "b2_sigma" ≠ ofString "b2_m" := by decide
  have q2_0 : ofString "b2_iv" ≠ ofString "heap_ptr" := by decide
  have q2_1 : ofString "b2_iv" ≠ ofString "b2_sigma" := by decide
  have q2_3 : ofString "b2_iv" ≠ ofString "b2_round" := by decide
  have q2_4 : ofString "b2_iv" ≠ ofString "b2_v" := by decide
  have q2_5 : ofString "b2_iv" ≠ ofString "b2_m" := by decide
  have q3_0 : ofString "b2_round" ≠ ofString "heap_ptr" := by decide
  have q3_1 : ofString "b2_round" ≠ ofString "b2_sigma" := by decide
  have q3_2 : ofString "b2_round" ≠ ofString "b2_iv" := by decide
  have q3_4 : ofString "b2_round" ≠ ofString "b2_v" := by decide
  have q3_5 : ofString "b2_round" ≠ ofString "b2_m" := by decide
  have q4_0 : ofString "b2_v" ≠ ofString "heap_ptr" := by decide
  have q4_1 : ofString "b2_v" ≠ ofString "b2_sigma" := by decide
  have q4_2 : ofString "b2_v" ≠ ofString "b2_iv" := by decide
  have q4_3 : ofString "b2_v" ≠ ofString "b2_round" := by decide
  have q4_5 : ofString "b2_v" ≠ ofString "b2_m" := by decide
  have q5_0 : ofString "b2_m" ≠ ofString "heap_ptr" := by decide
  have q5_1 : ofString "b2_m" ≠ ofString "b2_sigma" := by decide
  have q5_2 : ofString "b2_m" ≠ ofString "b2_iv" := by decide
  have q5_3 : ofString "b2_m" ≠ ofString "b2_round" := by decide
  have q5_4 : ofString "b2_m" ≠ ofString "b2_v" := by decide
  obtain ⟨oiv,wiv⟩ := words (ofString "b2_iv") (by simp)
  obtain ⟨oround,wround⟩ := words (ofString "b2_round") (by simp)
  obtain ⟨ov,wv⟩ := words (ofString "b2_v") (by simp)
  obtain ⟨om,wm⟩ := words (ofString "b2_m") (by simp)
  rw [source_blake2Init_body] at run
  have guard : evaluateHOLFiniteState state
      (.ite (.cmp .notEqual (.var .global (ofString "b2_sigma")) (.const 0)) (.return (.const 0)) .skip) = (none,state) := by
    rw [evaluateHOLFiniteState_ite]
    simp [evalHOLExact,sigmaZero,Compiler.Encoders.Asm.wordCmpHOL,evaluateHOLFiniteState_skip]
  rw [bnSeqNone guard] at run
  have e80 := allocationEnd_aligned_exact H 80 aligned (by decide) (by simp [BitVec.toNat_add] <;> omega)
  have e144 := allocationEnd_aligned_exact (H + 80) 64 (by simp [BitVec.toNat_add] <;> omega) (by decide) (by simp [BitVec.toNat_add] <;> omega)
  have e408 := allocationEnd_aligned_exact (H + 80 + 64) 264 (by simp [BitVec.toNat_add] <;> omega) (by decide) (by simp [BitVec.toNat_add] <;> omega)
  have safe : AllocationPlanSafe H (blake2InitAllocations.map Prod.snd) := by
    simpa [blake2InitAllocations] using (allocationPlan_safe [80,64,264] H (by simp; omega)).1
  obtain ⟨ready,prefixRun,_,_,_,rcode,_,rglob,_⟩ := evaluate_globalAllocation_prefix state blake2InitAllocations
    blake2InitTail H code heap (by simp [blake2InitAllocations]; decide)
    (by intro e m; simp [blake2InitAllocations] at m; rcases m with rfl|rfl|rfl
        · exact ⟨0,sigmaZero⟩
        · exact ⟨oiv,wiv⟩
        · exact ⟨oround,wround⟩) safe (by simp [blake2InitAllocations]; omega)
  rw [prefixRun] at run
  simp only [globalAllocationGlobals,blake2InitAllocations] at rglob
  rw [e80,e144,e408] at rglob
  let s1 := setGlobalHOLFinite (ofString "b2_v") (.val (.word (H + 80 + 64 + 8))) ready
  have a1 : evaluateHOLFiniteState ready (.assign .global (ofString "b2_v") (.op .add [.var .global (ofString "b2_round"),.const 8])) = (none,s1) :=
    evaluate_assign_global_word ready _ _ ov _ (by rw [rglob]; simp [*,HolFiniteMapExact.lookup_update,FUPDATE,setGlobalHOLFinite]) (by simp [*,evalHOLExact,evalListHOLExact,wordOpHOL,wordOp,valueIsWord,valueWord,rglob,HolFiniteMapExact.lookup_update,FUPDATE,setGlobalHOLFinite])
  let s2 := setGlobalHOLFinite (ofString "b2_m") (.val (.word (H + 80 + 64 + 136))) s1
  have a2 : evaluateHOLFiniteState s1 (.assign .global (ofString "b2_m") (.op .add [.var .global (ofString "b2_round"),.const 136])) = (none,s2) :=
    evaluate_assign_global_word s1 _ _ om _ (by simp [*,s1,rglob,HolFiniteMapExact.lookup_update,FUPDATE,setGlobalHOLFinite]) (by simp [*,s1,evalHOLExact,evalListHOLExact,wordOpHOL,wordOp,valueIsWord,valueWord,rglob,HolFiniteMapExact.lookup_update,FUPDATE,setGlobalHOLFinite])
  unfold blake2InitTail at run
  rw [bnSeqNone a1,bnSeqNone a2] at run
  obtain ⟨mid,mg,_,_,_,run⟩ := StoreChain.returned (tail := .return (.const 0))
    (by simp only [globalConstantStores,blake2SigmaCells,blake2IvCells]
        repeat (apply StoreChain.cons)
        exact StoreChain.nil _) run
  simp [evaluateHOLFiniteState_return,evalHOLExact,shapeOfHOLExact] at run
  obtain ⟨hv,hp⟩ := run
  refine ⟨hv.symm,?_⟩
  rw [← hp]
  change mid.globals = _
  rw [mg]
  simp only [s2,s1,setGlobalHOLFinite]
  rw [rglob]
  simp only [blake2InitGlobals,BitVec.add_assoc,BitVec.reduceAdd]
  rfl

#print axioms blake2Init_body_returned

/-- The actual call `blake2_init()` on first initialization from aligned heap H:
at most 7 ticks in every outcome, no timeout, and on normal continuation exactly
`blake2InitGlobals` with caller locals, code and memory domain preserved. -/
theorem evaluate_blake2Init_call_outcome {F : Type} (state : PanSemStateFiniteExact 64 F) (H : BitVec 64)
    (code : state.code = originalRuntimeCode)
    (heap : state.globals.lookup (ofString "heap_ptr") = some (.val (.word H)))
    (aligned : H.toNat % 8 = 0) (room : H.toNat + 512 ≤ 33806089496)
    (sigmaZero : state.globals.lookup (ofString "b2_sigma") = some (.val (.word 0)))
    (words : ∀ name ∈ [ofString "b2_iv",ofString "b2_round",ofString "b2_v",ofString "b2_m"],
      ∃ word : BitVec 64, state.globals.lookup name = some (.val (.word word)))
    (budget : 7 ≤ state.clock) :
    let result := evaluateHOLFiniteState state (.call (some (none,none)) (ofString "blake2_init") [])
    state.clock ≤ result.2.clock + 7 ∧ result.2.clock ≤ state.clock ∧ result.1 ≠ some .timeOut ∧
      (result.1 = none → result.2.globals = blake2InitGlobals state.globals H ∧ result.2.locals = state.locals ∧
        result.2.code = state.code ∧ result.2.memaddrs = state.memaddrs) := by
  have bounded := evaluate_blake2Init_call_bounded state none [] code budget
  refine ⟨bounded.1,bounded.2.1,bounded.2.2,?_⟩
  have lookup := pan_no_args_lookup state.code.lookup (ofString "blake2_init")
    (sourceFunctionBody Guest.guestFn_blake2_init) (by rw [code]; exact originalRuntimeCode_blake2Init_lookup)
  have nonzero : state.clock ≠ 0 := by omega
  rw [evaluateHOLFiniteState_call]
  simp only [evalListHOLFinite,evalListHOLExact]
  rw [lookup]
  simp only [if_neg nonzero]
  cases run : evaluateHOLFiniteState (callEntryStateHOLFinite state HolFiniteMapExact.empty)
      (sourceFunctionBody Guest.guestFn_blake2_init) with
  | mk result post =>
    rcases result with _ | (_ | _ | _ | _ | w | _ | _)
    all_goals first
      | (simp; done)
      | skip
    obtain ⟨_,globals⟩ := blake2Init_body_returned (callEntryStateHOLFinite state HolFiniteMapExact.empty) post H w
      code heap aligned room sigmaZero words (by change 3 ≤ state.clock - 1; omega) run
    have meta' := evaluateHOLFiniteState_metadata (callEntryStateHOLFinite state HolFiniteMapExact.empty)
      (sourceFunctionBody Guest.guestFn_blake2_init)
    rw [run] at meta'
    dsimp only
    split
    · intro _
      exact ⟨globals,rfl,meta'.1,meta'.2.1⟩
    · simp

#print axioms evaluate_blake2Init_call_outcome

/-- At the actual entry heap 2713730208 the normal continuation ends with heap_ptr 2713730616. -/
theorem blake2InitGlobals_actual_heap (g : HolFiniteMapExact MlS (ValueHOL 64)) :
    (blake2InitGlobals g 2713730208).lookup (ofString "heap_ptr") = some (.val (.word 2713730616)) := by
  have a : ofString "b2_m" ≠ ofString "heap_ptr" := by decide
  have b : ofString "b2_v" ≠ ofString "heap_ptr" := by decide
  have c : ofString "b2_round" ≠ ofString "heap_ptr" := by decide
  simp [blake2InitGlobals,HolFiniteMapExact.lookup_update,FUPDATE,a,b,c]

theorem evaluate_blake2Init_call_at_entry_heap {F : Type} (state : PanSemStateFiniteExact 64 F)
    (code : state.code = originalRuntimeCode)
    (heap : state.globals.lookup (ofString "heap_ptr") = some (.val (.word 2713730208)))
    (sigmaZero : state.globals.lookup (ofString "b2_sigma") = some (.val (.word 0)))
    (words : ∀ name ∈ [ofString "b2_iv",ofString "b2_round",ofString "b2_v",ofString "b2_m"],
      ∃ word : BitVec 64, state.globals.lookup name = some (.val (.word word)))
    (budget : 7 ≤ state.clock) :
    let result := evaluateHOLFiniteState state (.call (some (none,none)) (ofString "blake2_init") [])
    state.clock ≤ result.2.clock + 7 ∧ result.2.clock ≤ state.clock ∧ result.1 ≠ some .timeOut ∧
      (result.1 = none → result.2.globals = blake2InitGlobals state.globals 2713730208 ∧
        result.2.globals.lookup (ofString "heap_ptr") = some (.val (.word 2713730616)) ∧
        result.2.locals = state.locals ∧ result.2.code = state.code ∧ result.2.memaddrs = state.memaddrs) := by
  obtain ⟨a,b,c,d⟩ := evaluate_blake2Init_call_outcome state 2713730208 code heap (by decide) (by decide)
    sigmaZero words budget
  refine ⟨a,b,c,fun normal => ?_⟩
  obtain ⟨g,l,k,m⟩ := d normal
  exact ⟨g,by rw [g]; exact blake2InitGlobals_actual_heap _,l,k,m⟩

#print axioms evaluate_blake2Init_call_at_entry_heap
end InitECandidate.Runtime
