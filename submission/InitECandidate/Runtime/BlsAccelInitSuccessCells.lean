import InitECandidate.Runtime.BlsAccelInitSuccess
import InitECandidate.Runtime.BlsConstsInitSuccessCells
import InitECandidate.Runtime.BlsArenaCells
import InitECandidate.Runtime.MemzeroAlignedCallCells
import InitECandidate.Runtime.MemcpyAlignedCallCells
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
theorem evaluate_fpAccelInit_call_first_cells {F : Type} (state : PanSemStateFiniteExact 64 F) (C P : BitVec 64)
    (code : state.code = originalRuntimeCode)
    (heap : state.globals.lookup (ofString "heap_ptr") = some (.val (.word P)))
    (consts : state.globals.lookup (ofString "bls_c") = some (.val (.word C))) (nonzero : C ≠ 0)
    (alignedC : C.toNat % 8 = 0) (alignedP : P.toNat % 8 = 0) (order : C.toNat + 96 ≤ P.toNat)
    (room : P.toNat + 2048 ≤ 33806089496)
    (zero : state.globals.lookup (ofString "fp_accel_params") = some (.val (.word 0)))
    (words : ∀ name ∈ [ofString "fp_accel_a",ofString "fp_accel_b",ofString "fp_accel_zero",ofString "fp_accel_d"],
      ∃ word : BitVec 64, state.globals.lookup name = some (.val (.word word)))
    (arena : ∀ address : BitVec 64, address.toNat % 8 = 0 → C.toNat ≤ address.toNat → address.toNat < 33806089496 → state.memaddrs address)
    (budget : 102 ≤ state.clock) :
    ∃ post : PanSemStateFiniteExact 64 F,
      evaluateHOLFiniteState state (.call (some (none,none)) (ofString "fp_accel_init") []) = (none,post) ∧
      state.clock ≤ post.clock + 102 ∧ post.clock ≤ state.clock ∧ post.locals = state.locals ∧
      post.code = state.code ∧ post.memaddrs = state.memaddrs ∧ post.globals = fpAccelGlobals state.globals P := by
  have q0_1 : ofString "heap_ptr" ≠ ofString "fp_accel_params" := by decide
  have q0_2 : ofString "heap_ptr" ≠ ofString "fp_accel_a" := by decide
  have q0_3 : ofString "heap_ptr" ≠ ofString "fp_accel_b" := by decide
  have q0_4 : ofString "heap_ptr" ≠ ofString "fp_accel_zero" := by decide
  have q0_5 : ofString "heap_ptr" ≠ ofString "fp_accel_d" := by decide
  have q0_6 : ofString "heap_ptr" ≠ ofString "bls_c" := by decide
  have q1_0 : ofString "fp_accel_params" ≠ ofString "heap_ptr" := by decide
  have q1_2 : ofString "fp_accel_params" ≠ ofString "fp_accel_a" := by decide
  have q1_3 : ofString "fp_accel_params" ≠ ofString "fp_accel_b" := by decide
  have q1_4 : ofString "fp_accel_params" ≠ ofString "fp_accel_zero" := by decide
  have q1_5 : ofString "fp_accel_params" ≠ ofString "fp_accel_d" := by decide
  have q1_6 : ofString "fp_accel_params" ≠ ofString "bls_c" := by decide
  have q2_0 : ofString "fp_accel_a" ≠ ofString "heap_ptr" := by decide
  have q2_1 : ofString "fp_accel_a" ≠ ofString "fp_accel_params" := by decide
  have q2_3 : ofString "fp_accel_a" ≠ ofString "fp_accel_b" := by decide
  have q2_4 : ofString "fp_accel_a" ≠ ofString "fp_accel_zero" := by decide
  have q2_5 : ofString "fp_accel_a" ≠ ofString "fp_accel_d" := by decide
  have q2_6 : ofString "fp_accel_a" ≠ ofString "bls_c" := by decide
  have q3_0 : ofString "fp_accel_b" ≠ ofString "heap_ptr" := by decide
  have q3_1 : ofString "fp_accel_b" ≠ ofString "fp_accel_params" := by decide
  have q3_2 : ofString "fp_accel_b" ≠ ofString "fp_accel_a" := by decide
  have q3_4 : ofString "fp_accel_b" ≠ ofString "fp_accel_zero" := by decide
  have q3_5 : ofString "fp_accel_b" ≠ ofString "fp_accel_d" := by decide
  have q3_6 : ofString "fp_accel_b" ≠ ofString "bls_c" := by decide
  have q4_0 : ofString "fp_accel_zero" ≠ ofString "heap_ptr" := by decide
  have q4_1 : ofString "fp_accel_zero" ≠ ofString "fp_accel_params" := by decide
  have q4_2 : ofString "fp_accel_zero" ≠ ofString "fp_accel_a" := by decide
  have q4_3 : ofString "fp_accel_zero" ≠ ofString "fp_accel_b" := by decide
  have q4_5 : ofString "fp_accel_zero" ≠ ofString "fp_accel_d" := by decide
  have q4_6 : ofString "fp_accel_zero" ≠ ofString "bls_c" := by decide
  have q5_0 : ofString "fp_accel_d" ≠ ofString "heap_ptr" := by decide
  have q5_1 : ofString "fp_accel_d" ≠ ofString "fp_accel_params" := by decide
  have q5_2 : ofString "fp_accel_d" ≠ ofString "fp_accel_a" := by decide
  have q5_3 : ofString "fp_accel_d" ≠ ofString "fp_accel_b" := by decide
  have q5_4 : ofString "fp_accel_d" ≠ ofString "fp_accel_zero" := by decide
  have q5_6 : ofString "fp_accel_d" ≠ ofString "bls_c" := by decide
  have q6_0 : ofString "bls_c" ≠ ofString "heap_ptr" := by decide
  have q6_1 : ofString "bls_c" ≠ ofString "fp_accel_params" := by decide
  have q6_2 : ofString "bls_c" ≠ ofString "fp_accel_a" := by decide
  have q6_3 : ofString "bls_c" ≠ ofString "fp_accel_b" := by decide
  have q6_4 : ofString "bls_c" ≠ ofString "fp_accel_zero" := by decide
  have q6_5 : ofString "bls_c" ≠ ofString "fp_accel_d" := by decide
  obtain ⟨oa,wa⟩ := words (ofString "fp_accel_a") (by simp)
  obtain ⟨ob,wb⟩ := words (ofString "fp_accel_b") (by simp)
  obtain ⟨oz,wz⟩ := words (ofString "fp_accel_zero") (by simp)
  obtain ⟨od,wd⟩ := words (ofString "fp_accel_d") (by simp)
  let E := callEntryStateHOLFinite state HolFiniteMapExact.empty
  have guard : evaluateHOLFiniteState E
      (.ite (.cmp .notEqual (.var .global (ofString "fp_accel_params")) (.const 0)) (.return (.const 0)) .skip) = (none,E) := by
    rw [evaluateHOLFiniteState_ite]
    simp [E,callEntryStateHOLFinite,evalHOLExact,zero,Compiler.Encoders.Asm.wordCmpHOL,evaluateHOLFiniteState_skip]
  have constsCall := evaluate_blsConstsInit_call_installed E C code consts nonzero (by change 1 ≤ state.clock - 1; omega)
  let E1 : PanSemStateFiniteExact 64 F := {E with clock := E.clock - 1}
  obtain ⟨req,fin,_,_⟩ := allocation_success_bounds P 240 (by simp; omega)
  obtain ⟨r1,a1,c1,_,_,k1,d1,_,n1,h1,o1⟩ := evaluate_alloc_global_call E1 (.const 240) P 240 0
    (ofString "fp_accel_params") (by simp [evalListHOLFinite,evalListHOLExact,evalHOLExact]) code
    (by change state.clock - 1 - 1 ≠ 0; omega) heap zero (by decide) req fin
  have finish := allocationEnd_aligned_exact P 240 alignedP (by decide) (by simp; omega)
  rw [finish] at h1
  have g1 := alloc_globals_eq E1 r1 _ _ _ (by decide) n1 h1 o1
  let s1 := setGlobalHOLFinite (ofString "fp_accel_a") (.val (.word P)) r1
  have e1 : evaluateHOLFiniteState r1 (.assign .global (ofString "fp_accel_a") (.var .global (ofString "fp_accel_params"))) = (none,s1) :=
    evaluate_assign_global_word r1 _ _ oa P (by simp [*,g1,E1,E,callEntryStateHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,setGlobalHOLFinite]) (by simp [*,evalHOLExact,evalListHOLExact,wordOpHOL,wordOp,valueIsWord,valueWord,g1,HolFiniteMapExact.lookup_update,FUPDATE,setGlobalHOLFinite])
  let s2 := setGlobalHOLFinite (ofString "fp_accel_b") (.val (.word (P + 48))) s1
  have e2 : evaluateHOLFiniteState s1 (.assign .global (ofString "fp_accel_b") (.op .add [.var .global (ofString "fp_accel_params"),.const 48])) = (none,s2) :=
    evaluate_assign_global_word s1 _ _ ob _ (by simp [*,s1,g1,E1,E,callEntryStateHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,setGlobalHOLFinite]) (by simp [*,s1,evalHOLExact,evalListHOLExact,wordOpHOL,wordOp,valueIsWord,valueWord,g1,HolFiniteMapExact.lookup_update,FUPDATE,setGlobalHOLFinite])
  let s3 := setGlobalHOLFinite (ofString "fp_accel_zero") (.val (.word (P + 96))) s2
  have e3 : evaluateHOLFiniteState s2 (.assign .global (ofString "fp_accel_zero") (.op .add [.var .global (ofString "fp_accel_params"),.const 96])) = (none,s3) :=
    evaluate_assign_global_word s2 _ _ oz _ (by simp [*,s1,s2,g1,E1,E,callEntryStateHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,setGlobalHOLFinite]) (by simp [*,s1,s2,evalHOLExact,evalListHOLExact,wordOpHOL,wordOp,valueIsWord,valueWord,g1,HolFiniteMapExact.lookup_update,FUPDATE,setGlobalHOLFinite])
  let s4 := setGlobalHOLFinite (ofString "fp_accel_d") (.val (.word (P + 192))) s3
  have e4 : evaluateHOLFiniteState s3 (.assign .global (ofString "fp_accel_d") (.op .add [.var .global (ofString "fp_accel_params"),.const 192])) = (none,s4) :=
    evaluate_assign_global_word s3 _ _ od _ (by simp [*,s1,s2,s3,g1,E1,E,callEntryStateHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,setGlobalHOLFinite]) (by simp [*,s1,s2,s3,evalHOLExact,evalListHOLExact,wordOpHOL,wordOp,valueIsWord,valueWord,g1,HolFiniteMapExact.lookup_update,FUPDATE,setGlobalHOLFinite])
  have s4m : s4.memaddrs = state.memaddrs := d1
  have s4c : s4.code = originalRuntimeCode := k1.trans code
  have s4k : s4.clock = state.clock - 3 := by change r1.clock = _; rw [c1]; change state.clock - 1 - 1 - 1 = _; omega
  have p96 : (P + 96).toNat = P.toNat + 96 := by rw [BitVec.toNat_add_of_lt (by simp; omega)]; simp
  obtain ⟨m1,z1,_,zb1,zb2,zg,zc,zm,_,zl,_⟩ := evaluate_memzero_aligned_call_cells s4 (.var .global (ofString "fp_accel_zero")) (.const 48)
    (P + 96) 48 (by simp [*,s1,s2,s3,s4,evalListHOLFinite,evalHOLExact,evalListHOLExact,wordOpHOL,wordOp,valueIsWord,valueWord,g1,HolFiniteMapExact.lookup_update,FUPDATE,setGlobalHOLFinite]) s4c (by rw [s4k]; simp; omega)
    (by rw [p96]; simp; omega) (by rw [p96]; omega)
    (fun k hk => by rw [s4m]; exact (arena_offset_byte_cell state C (P + 96) k alignedC (by omega) (by rw [p96]; simp at hk; omega) arena))
  have p144 : (P + 144).toNat = P.toNat + 144 := by rw [BitVec.toNat_add_of_lt (by simp; omega)]; simp
  have c48 : (C + 48).toNat = C.toNat + 48 := by rw [BitVec.toNat_add_of_lt (by simp; omega)]; simp
  have m1m : m1.memaddrs = state.memaddrs := zm.trans s4m
  obtain ⟨m2,y1,_,yb1,yb2,yg,yc,ym,_,yl⟩ := evaluate_memcpy_aligned_call_cells m1
    (.op .add [.var .global (ofString "fp_accel_params"),.const 144]) (.op .add [.var .global (ofString "bls_c"),.const 48]) (.const 48)
    (P + 144) (C + 48) 48 0 0 (by rw [p144]; simp; omega) (by rw [p144]; omega) (by rw [c48]; omega)
    (by have := zb1; rw [s4k] at this; simp at this ⊢; omega)
    (fun k hk kAligned => by rw [m1m]; exact (arena_offset_word_cell state C (P + 144) k alignedC (by omega) (by rw [p144]; simp at hk; omega) arena (by rw [p144]; omega) kAligned))
    (fun k hk => by rw [m1m]; exact (arena_offset_byte_cell state C (P + 144) k alignedC (by omega) (by rw [p144]; simp at hk; omega) arena))
    (fun k hk kAligned => by rw [m1m]; exact (arena_offset_word_cell state C (C + 48) k alignedC (by omega) (by rw [c48]; simp at hk; omega) arena (by rw [c48]; omega) kAligned))
    (fun k hk => by rw [m1m]; exact (arena_offset_byte_cell state C (C + 48) k alignedC (by omega) (by rw [c48]; simp at hk; omega) arena))
    (fun _ _ slot inside => by simp at inside) (fun _ _ slot inside => by simp at inside) (zc.trans s4c)
    (by simp [*,s1,s2,s3,s4,evalListHOLFinite,evalHOLExact,evalListHOLExact,wordOpHOL,wordOp,valueIsWord,valueWord,g1,E1,E,callEntryStateHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,setGlobalHOLFinite])
  have constsCall' : evaluateHOLFiniteState E (.call (some (none,none)) (ofString "bls_consts_init") []) = (none,E1) := constsCall
  have body : evaluateHOLFiniteState E (sourceFunctionBody Guest.guestFn_fp_accel_init) =
      (some (.returned (.val (.word 0))),emptyLocalsHOLFinite m2) := by
    rw [source_fpAccelInit_body,bnSeqNone guard,bnSeqNone constsCall',bnSeqNone a1,bnSeqNone e1,bnSeqNone e2,bnSeqNone e3,
      bnSeqNone e4,bnSeqNone z1,bnSeqNone y1]
    simp [evaluateHOLFiniteState_return,evalHOLExact,shapeOfHOLExact]
  have lookup := pan_no_args_lookup state.code.lookup (ofString "fp_accel_init")
    (sourceFunctionBody Guest.guestFn_fp_accel_init) (by rw [code]; exact originalRuntimeCode_fpAccelInit_lookup)
  have call := evaluateHOLFiniteState_call_return_caller_locals state none (ofString "fp_accel_init") [] []
    (sourceFunctionBody Guest.guestFn_fp_accel_init) HolFiniteMapExact.empty .one (.val (.word 0)) _
    rfl lookup (by omega) body (by simp [shapeOfHOLExact,shapeEqHOL])
  refine ⟨_,call,?_,?_,rfl,yc.trans (zc.trans (k1.trans rfl)),ym.trans m1m,?_⟩
  · change state.clock ≤ m2.clock + 102
    rw [s4k] at zb1
    simp at zb1 yb1
    omega
  · change m2.clock ≤ state.clock
    rw [s4k] at zb2
    omega
  · change m2.globals = _
    rw [yg,zg]
    simp only [s4,s3,s2,s1,setGlobalHOLFinite]
    rw [g1]
    rfl

#print axioms evaluate_fpAccelInit_call_first_cells
end InitECandidate.Runtime
