import InitECandidate.Runtime.BlsAccelInitSuccess
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

/-- Globals after the first fp2_accel_init from aligned heap P. -/
def fp2AccelInitGlobals (g : HolFiniteMapExact MlS (ValueHOL 64)) (P : BitVec 64) : HolFiniteMapExact MlS (ValueHOL 64) :=
  (((g.update (ofString "heap_ptr",.val (.word (P + 192)))).update (ofString "fp2_accel_params",.val (.word P))).update
    (ofString "fp2_accel_f1",.val (.word P))).update (ofString "fp2_accel_f2",.val (.word (P + 96)))

theorem evaluate_fp2AccelInit_call_first {F : Type} (state : PanSemStateFiniteExact 64 F) (C P : BitVec 64)
    (code : state.code = originalRuntimeCode)
    (heap : state.globals.lookup (ofString "heap_ptr") = some (.val (.word P)))
    (consts : state.globals.lookup (ofString "bls_c") = some (.val (.word C))) (nonzero : C ≠ 0)
    (alignedP : P.toNat % 8 = 0) (room : P.toNat + 2048 ≤ 33806089496)
    (zero : state.globals.lookup (ofString "fp2_accel_params") = some (.val (.word 0)))
    (w1 : ∃ word : BitVec 64, state.globals.lookup (ofString "fp2_accel_f1") = some (.val (.word word)))
    (w2 : ∃ word : BitVec 64, state.globals.lookup (ofString "fp2_accel_f2") = some (.val (.word word)))
    (budget : 4 ≤ state.clock) :
    ∃ post : PanSemStateFiniteExact 64 F,
      evaluateHOLFiniteState state (.call (some (none,none)) (ofString "fp2_accel_init") []) = (none,post) ∧
      post.clock = state.clock - 3 ∧ post.locals = state.locals ∧
      post.code = state.code ∧ post.memaddrs = state.memaddrs ∧ post.globals = fp2AccelInitGlobals state.globals P := by
  have q0_1 : ofString "heap_ptr" ≠ ofString "fp2_accel_params" := by decide
  have q0_2 : ofString "heap_ptr" ≠ ofString "fp2_accel_f1" := by decide
  have q0_3 : ofString "heap_ptr" ≠ ofString "fp2_accel_f2" := by decide
  have q0_4 : ofString "heap_ptr" ≠ ofString "bls_c" := by decide
  have q1_0 : ofString "fp2_accel_params" ≠ ofString "heap_ptr" := by decide
  have q1_2 : ofString "fp2_accel_params" ≠ ofString "fp2_accel_f1" := by decide
  have q1_3 : ofString "fp2_accel_params" ≠ ofString "fp2_accel_f2" := by decide
  have q1_4 : ofString "fp2_accel_params" ≠ ofString "bls_c" := by decide
  have q2_0 : ofString "fp2_accel_f1" ≠ ofString "heap_ptr" := by decide
  have q2_1 : ofString "fp2_accel_f1" ≠ ofString "fp2_accel_params" := by decide
  have q2_3 : ofString "fp2_accel_f1" ≠ ofString "fp2_accel_f2" := by decide
  have q2_4 : ofString "fp2_accel_f1" ≠ ofString "bls_c" := by decide
  have q3_0 : ofString "fp2_accel_f2" ≠ ofString "heap_ptr" := by decide
  have q3_1 : ofString "fp2_accel_f2" ≠ ofString "fp2_accel_params" := by decide
  have q3_2 : ofString "fp2_accel_f2" ≠ ofString "fp2_accel_f1" := by decide
  have q3_4 : ofString "fp2_accel_f2" ≠ ofString "bls_c" := by decide
  have q4_0 : ofString "bls_c" ≠ ofString "heap_ptr" := by decide
  have q4_1 : ofString "bls_c" ≠ ofString "fp2_accel_params" := by decide
  have q4_2 : ofString "bls_c" ≠ ofString "fp2_accel_f1" := by decide
  have q4_3 : ofString "bls_c" ≠ ofString "fp2_accel_f2" := by decide
  obtain ⟨ow1,h1w⟩ := w1
  obtain ⟨ow2,h2w⟩ := w2
  let E := callEntryStateHOLFinite state HolFiniteMapExact.empty
  have guard : evaluateHOLFiniteState E
      (.ite (.cmp .notEqual (.var .global (ofString "fp2_accel_params")) (.const 0)) (.return (.const 0)) .skip) = (none,E) := by
    rw [evaluateHOLFiniteState_ite]
    simp [E,callEntryStateHOLFinite,evalHOLExact,zero,Compiler.Encoders.Asm.wordCmpHOL,evaluateHOLFiniteState_skip]
  have constsCall := evaluate_blsConstsInit_call_installed E C code consts nonzero (by change 1 ≤ state.clock - 1; omega)
  let E1 : PanSemStateFiniteExact 64 F := {E with clock := E.clock - 1}
  have constsCall' : evaluateHOLFiniteState E (.call (some (none,none)) (ofString "bls_consts_init") []) = (none,E1) := constsCall
  obtain ⟨req,fin,_,_⟩ := allocation_success_bounds P 192 (by simp; omega)
  obtain ⟨r1,a1,c1,_,_,k1,d1,_,n1,h1,o1⟩ := evaluate_alloc_global_call E1 (.const 192) P 192 0
    (ofString "fp2_accel_params") (by simp [evalListHOLFinite,evalListHOLExact,evalHOLExact]) code
    (by change state.clock - 1 - 1 ≠ 0; omega) heap zero (by decide) req fin
  have finish := allocationEnd_aligned_exact P 192 alignedP (by decide) (by simp; omega)
  rw [finish] at h1
  have g1 := alloc_globals_eq E1 r1 _ _ _ (by decide) n1 h1 o1
  let s1 := setGlobalHOLFinite (ofString "fp2_accel_f1") (.val (.word P)) r1
  have e1 : evaluateHOLFiniteState r1 (.assign .global (ofString "fp2_accel_f1") (.var .global (ofString "fp2_accel_params"))) = (none,s1) :=
    evaluate_assign_global_word r1 _ _ ow1 P (by simp [*,g1,E1,E,callEntryStateHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,setGlobalHOLFinite]) (by simp [*,evalHOLExact,evalListHOLExact,wordOpHOL,wordOp,valueIsWord,valueWord,g1,HolFiniteMapExact.lookup_update,FUPDATE,setGlobalHOLFinite])
  let s2 := setGlobalHOLFinite (ofString "fp2_accel_f2") (.val (.word (P + 96))) s1
  have e2 : evaluateHOLFiniteState s1 (.assign .global (ofString "fp2_accel_f2") (.op .add [.var .global (ofString "fp2_accel_params"),.const 96])) = (none,s2) :=
    evaluate_assign_global_word s1 _ _ ow2 _ (by simp [*,s1,g1,E1,E,callEntryStateHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,setGlobalHOLFinite]) (by simp [*,s1,evalHOLExact,evalListHOLExact,wordOpHOL,wordOp,valueIsWord,valueWord,g1,HolFiniteMapExact.lookup_update,FUPDATE,setGlobalHOLFinite])
  have body : evaluateHOLFiniteState E (sourceFunctionBody Guest.guestFn_fp2_accel_init) =
      (some (.returned (.val (.word 0))),emptyLocalsHOLFinite s2) := by
    rw [source_fp2AccelInit_body,bnSeqNone guard,bnSeqNone constsCall',bnSeqNone a1,bnSeqNone e1,bnSeqNone e2]
    simp [evaluateHOLFiniteState_return,evalHOLExact,shapeOfHOLExact]
  have lookup := pan_no_args_lookup state.code.lookup (ofString "fp2_accel_init")
    (sourceFunctionBody Guest.guestFn_fp2_accel_init) (by rw [code]; exact originalRuntimeCode_fp2AccelInit_lookup)
  have call := evaluateHOLFiniteState_call_return_caller_locals state none (ofString "fp2_accel_init") [] []
    (sourceFunctionBody Guest.guestFn_fp2_accel_init) HolFiniteMapExact.empty .one (.val (.word 0)) _
    rfl lookup (by omega) body (by simp [shapeOfHOLExact,shapeEqHOL])
  refine ⟨_,call,?_,rfl,k1.trans rfl,d1,?_⟩
  · change r1.clock = _; rw [c1]; change state.clock - 1 - 1 - 1 = _; omega
  · change s2.globals = _
    simp only [s2,s1,setGlobalHOLFinite]
    rw [g1]
    rfl

#print axioms evaluate_fp2AccelInit_call_first

/-- Globals after the first bls_g1_accel_init from aligned heap P. -/
def blsG1AccelInitGlobals (g : HolFiniteMapExact MlS (ValueHOL 64)) (P : BitVec 64) : HolFiniteMapExact MlS (ValueHOL 64) :=
  (((g.update (ofString "heap_ptr",.val (.word (P + 192)))).update (ofString "bls_g1_accel_params",.val (.word P))).update
    (ofString "bls_g1_accel_p1",.val (.word P))).update (ofString "bls_g1_accel_p2",.val (.word (P + 96)))

theorem evaluate_blsG1AccelInit_call_first {F : Type} (state : PanSemStateFiniteExact 64 F) (C P : BitVec 64)
    (code : state.code = originalRuntimeCode)
    (heap : state.globals.lookup (ofString "heap_ptr") = some (.val (.word P)))
    (consts : state.globals.lookup (ofString "bls_c") = some (.val (.word C))) (nonzero : C ≠ 0)
    (alignedP : P.toNat % 8 = 0) (room : P.toNat + 2048 ≤ 33806089496)
    (zero : state.globals.lookup (ofString "bls_g1_accel_params") = some (.val (.word 0)))
    (w1 : ∃ word : BitVec 64, state.globals.lookup (ofString "bls_g1_accel_p1") = some (.val (.word word)))
    (w2 : ∃ word : BitVec 64, state.globals.lookup (ofString "bls_g1_accel_p2") = some (.val (.word word)))
    (budget : 4 ≤ state.clock) :
    ∃ post : PanSemStateFiniteExact 64 F,
      evaluateHOLFiniteState state (.call (some (none,none)) (ofString "bls_g1_accel_init") []) = (none,post) ∧
      post.clock = state.clock - 3 ∧ post.locals = state.locals ∧
      post.code = state.code ∧ post.memaddrs = state.memaddrs ∧ post.globals = blsG1AccelInitGlobals state.globals P := by
  have q0_1 : ofString "heap_ptr" ≠ ofString "bls_g1_accel_params" := by decide
  have q0_2 : ofString "heap_ptr" ≠ ofString "bls_g1_accel_p1" := by decide
  have q0_3 : ofString "heap_ptr" ≠ ofString "bls_g1_accel_p2" := by decide
  have q0_4 : ofString "heap_ptr" ≠ ofString "bls_c" := by decide
  have q1_0 : ofString "bls_g1_accel_params" ≠ ofString "heap_ptr" := by decide
  have q1_2 : ofString "bls_g1_accel_params" ≠ ofString "bls_g1_accel_p1" := by decide
  have q1_3 : ofString "bls_g1_accel_params" ≠ ofString "bls_g1_accel_p2" := by decide
  have q1_4 : ofString "bls_g1_accel_params" ≠ ofString "bls_c" := by decide
  have q2_0 : ofString "bls_g1_accel_p1" ≠ ofString "heap_ptr" := by decide
  have q2_1 : ofString "bls_g1_accel_p1" ≠ ofString "bls_g1_accel_params" := by decide
  have q2_3 : ofString "bls_g1_accel_p1" ≠ ofString "bls_g1_accel_p2" := by decide
  have q2_4 : ofString "bls_g1_accel_p1" ≠ ofString "bls_c" := by decide
  have q3_0 : ofString "bls_g1_accel_p2" ≠ ofString "heap_ptr" := by decide
  have q3_1 : ofString "bls_g1_accel_p2" ≠ ofString "bls_g1_accel_params" := by decide
  have q3_2 : ofString "bls_g1_accel_p2" ≠ ofString "bls_g1_accel_p1" := by decide
  have q3_4 : ofString "bls_g1_accel_p2" ≠ ofString "bls_c" := by decide
  have q4_0 : ofString "bls_c" ≠ ofString "heap_ptr" := by decide
  have q4_1 : ofString "bls_c" ≠ ofString "bls_g1_accel_params" := by decide
  have q4_2 : ofString "bls_c" ≠ ofString "bls_g1_accel_p1" := by decide
  have q4_3 : ofString "bls_c" ≠ ofString "bls_g1_accel_p2" := by decide
  obtain ⟨ow1,h1w⟩ := w1
  obtain ⟨ow2,h2w⟩ := w2
  let E := callEntryStateHOLFinite state HolFiniteMapExact.empty
  have guard : evaluateHOLFiniteState E
      (.ite (.cmp .notEqual (.var .global (ofString "bls_g1_accel_params")) (.const 0)) (.return (.const 0)) .skip) = (none,E) := by
    rw [evaluateHOLFiniteState_ite]
    simp [E,callEntryStateHOLFinite,evalHOLExact,zero,Compiler.Encoders.Asm.wordCmpHOL,evaluateHOLFiniteState_skip]
  have constsCall := evaluate_blsConstsInit_call_installed E C code consts nonzero (by change 1 ≤ state.clock - 1; omega)
  let E1 : PanSemStateFiniteExact 64 F := {E with clock := E.clock - 1}
  have constsCall' : evaluateHOLFiniteState E (.call (some (none,none)) (ofString "bls_consts_init") []) = (none,E1) := constsCall
  obtain ⟨req,fin,_,_⟩ := allocation_success_bounds P 192 (by simp; omega)
  obtain ⟨r1,a1,c1,_,_,k1,d1,_,n1,h1,o1⟩ := evaluate_alloc_global_call E1 (.const 192) P 192 0
    (ofString "bls_g1_accel_params") (by simp [evalListHOLFinite,evalListHOLExact,evalHOLExact]) code
    (by change state.clock - 1 - 1 ≠ 0; omega) heap zero (by decide) req fin
  have finish := allocationEnd_aligned_exact P 192 alignedP (by decide) (by simp; omega)
  rw [finish] at h1
  have g1 := alloc_globals_eq E1 r1 _ _ _ (by decide) n1 h1 o1
  let s1 := setGlobalHOLFinite (ofString "bls_g1_accel_p1") (.val (.word P)) r1
  have e1 : evaluateHOLFiniteState r1 (.assign .global (ofString "bls_g1_accel_p1") (.var .global (ofString "bls_g1_accel_params"))) = (none,s1) :=
    evaluate_assign_global_word r1 _ _ ow1 P (by simp [*,g1,E1,E,callEntryStateHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,setGlobalHOLFinite]) (by simp [*,evalHOLExact,evalListHOLExact,wordOpHOL,wordOp,valueIsWord,valueWord,g1,HolFiniteMapExact.lookup_update,FUPDATE,setGlobalHOLFinite])
  let s2 := setGlobalHOLFinite (ofString "bls_g1_accel_p2") (.val (.word (P + 96))) s1
  have e2 : evaluateHOLFiniteState s1 (.assign .global (ofString "bls_g1_accel_p2") (.op .add [.var .global (ofString "bls_g1_accel_params"),.const 96])) = (none,s2) :=
    evaluate_assign_global_word s1 _ _ ow2 _ (by simp [*,s1,g1,E1,E,callEntryStateHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,setGlobalHOLFinite]) (by simp [*,s1,evalHOLExact,evalListHOLExact,wordOpHOL,wordOp,valueIsWord,valueWord,g1,HolFiniteMapExact.lookup_update,FUPDATE,setGlobalHOLFinite])
  have body : evaluateHOLFiniteState E (sourceFunctionBody Guest.guestFn_bls_g1_accel_init) =
      (some (.returned (.val (.word 0))),emptyLocalsHOLFinite s2) := by
    rw [source_blsG1AccelInit_body,bnSeqNone guard,bnSeqNone constsCall',bnSeqNone a1,bnSeqNone e1,bnSeqNone e2]
    simp [evaluateHOLFiniteState_return,evalHOLExact,shapeOfHOLExact]
  have lookup := pan_no_args_lookup state.code.lookup (ofString "bls_g1_accel_init")
    (sourceFunctionBody Guest.guestFn_bls_g1_accel_init) (by rw [code]; exact originalRuntimeCode_blsG1AccelInit_lookup)
  have call := evaluateHOLFiniteState_call_return_caller_locals state none (ofString "bls_g1_accel_init") [] []
    (sourceFunctionBody Guest.guestFn_bls_g1_accel_init) HolFiniteMapExact.empty .one (.val (.word 0)) _
    rfl lookup (by omega) body (by simp [shapeOfHOLExact,shapeEqHOL])
  refine ⟨_,call,?_,rfl,k1.trans rfl,d1,?_⟩
  · change r1.clock = _; rw [c1]; change state.clock - 1 - 1 - 1 = _; omega
  · change s2.globals = _
    simp only [s2,s1,setGlobalHOLFinite]
    rw [g1]
    rfl

#print axioms evaluate_blsG1AccelInit_call_first
end InitECandidate.Runtime
