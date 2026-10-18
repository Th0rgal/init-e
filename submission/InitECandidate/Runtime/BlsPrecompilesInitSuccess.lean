import InitECandidate.Runtime.BlsLibInitSuccess
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

/-- Globals after the first bls_precompiles_init from aligned heap H. -/
def blsInitGlobals (g : HolFiniteMapExact MlS (ValueHOL 64)) (H : BitVec 64) : HolFiniteMapExact MlS (ValueHOL 64) :=
  ((blsLibGlobals g H).update (ofString "heap_ptr",.val (.word (H + 9808)))).update (ofString "bls_discount",.val (.word (H + 7760)))

/-- The actual call `bls_precompiles_init()` on first initialization from aligned
heap H: returns normally within 114 ticks, installs the BLS constant table and
the Fp/Fp2/G1 accelerator blocks and the discount table, and leaves heap_ptr at
H+9808. Caller locals, code and memory domain are preserved. -/
theorem evaluate_blsPrecompilesInit_call_first {F : Type} (state : PanSemStateFiniteExact 64 F) (H : BitVec 64)
    (code : state.code = originalRuntimeCode)
    (heap : state.globals.lookup (ofString "heap_ptr") = some (.val (.word H)))
    (aligned : H.toNat % 8 = 0) (positive : 0 < H.toNat) (room : H.toNat + 12000 ≤ 33806089496)
    (discountZero : state.globals.lookup (ofString "bls_discount") = some (.val (.word 0)))
    (constsZero : state.globals.lookup (ofString "bls_c") = some (.val (.word 0)))
    (fpZero : state.globals.lookup (ofString "fp_accel_params") = some (.val (.word 0)))
    (fp2Zero : state.globals.lookup (ofString "fp2_accel_params") = some (.val (.word 0)))
    (g1Zero : state.globals.lookup (ofString "bls_g1_accel_params") = some (.val (.word 0)))
    (words : ∀ name ∈ blsLibWordNames, ∃ word : BitVec 64, state.globals.lookup name = some (.val (.word word)))
    (arena : ∀ address : BitVec 64, H.toNat ≤ address.toNat → address.toNat < 33806089496 → state.memaddrs address)
    (budget : 114 ≤ state.clock) :
    ∃ post : PanSemStateFiniteExact 64 F,
      evaluateHOLFiniteState state (.call (some (none,none)) (ofString "bls_precompiles_init") []) = (none,post) ∧
      state.clock ≤ post.clock + 114 ∧ post.clock ≤ state.clock ∧ post.locals = state.locals ∧
      post.code = state.code ∧ post.memaddrs = state.memaddrs ∧ post.globals = blsInitGlobals state.globals H := by
  have q0_1 : ofString "heap_ptr" ≠ ofString "bls_c" := by decide
  have q0_2 : ofString "heap_ptr" ≠ ofString "fp_accel_params" := by decide
  have q0_3 : ofString "heap_ptr" ≠ ofString "fp_accel_a" := by decide
  have q0_4 : ofString "heap_ptr" ≠ ofString "fp_accel_b" := by decide
  have q0_5 : ofString "heap_ptr" ≠ ofString "fp_accel_zero" := by decide
  have q0_6 : ofString "heap_ptr" ≠ ofString "fp_accel_d" := by decide
  have q0_7 : ofString "heap_ptr" ≠ ofString "fp2_accel_params" := by decide
  have q0_8 : ofString "heap_ptr" ≠ ofString "fp2_accel_f1" := by decide
  have q0_9 : ofString "heap_ptr" ≠ ofString "fp2_accel_f2" := by decide
  have q0_10 : ofString "heap_ptr" ≠ ofString "bls_g1_accel_params" := by decide
  have q0_11 : ofString "heap_ptr" ≠ ofString "bls_g1_accel_p1" := by decide
  have q0_12 : ofString "heap_ptr" ≠ ofString "bls_g1_accel_p2" := by decide
  have q0_13 : ofString "heap_ptr" ≠ ofString "bls_discount" := by decide
  have q1_0 : ofString "bls_c" ≠ ofString "heap_ptr" := by decide
  have q1_2 : ofString "bls_c" ≠ ofString "fp_accel_params" := by decide
  have q1_3 : ofString "bls_c" ≠ ofString "fp_accel_a" := by decide
  have q1_4 : ofString "bls_c" ≠ ofString "fp_accel_b" := by decide
  have q1_5 : ofString "bls_c" ≠ ofString "fp_accel_zero" := by decide
  have q1_6 : ofString "bls_c" ≠ ofString "fp_accel_d" := by decide
  have q1_7 : ofString "bls_c" ≠ ofString "fp2_accel_params" := by decide
  have q1_8 : ofString "bls_c" ≠ ofString "fp2_accel_f1" := by decide
  have q1_9 : ofString "bls_c" ≠ ofString "fp2_accel_f2" := by decide
  have q1_10 : ofString "bls_c" ≠ ofString "bls_g1_accel_params" := by decide
  have q1_11 : ofString "bls_c" ≠ ofString "bls_g1_accel_p1" := by decide
  have q1_12 : ofString "bls_c" ≠ ofString "bls_g1_accel_p2" := by decide
  have q1_13 : ofString "bls_c" ≠ ofString "bls_discount" := by decide
  have q2_0 : ofString "fp_accel_params" ≠ ofString "heap_ptr" := by decide
  have q2_1 : ofString "fp_accel_params" ≠ ofString "bls_c" := by decide
  have q2_3 : ofString "fp_accel_params" ≠ ofString "fp_accel_a" := by decide
  have q2_4 : ofString "fp_accel_params" ≠ ofString "fp_accel_b" := by decide
  have q2_5 : ofString "fp_accel_params" ≠ ofString "fp_accel_zero" := by decide
  have q2_6 : ofString "fp_accel_params" ≠ ofString "fp_accel_d" := by decide
  have q2_7 : ofString "fp_accel_params" ≠ ofString "fp2_accel_params" := by decide
  have q2_8 : ofString "fp_accel_params" ≠ ofString "fp2_accel_f1" := by decide
  have q2_9 : ofString "fp_accel_params" ≠ ofString "fp2_accel_f2" := by decide
  have q2_10 : ofString "fp_accel_params" ≠ ofString "bls_g1_accel_params" := by decide
  have q2_11 : ofString "fp_accel_params" ≠ ofString "bls_g1_accel_p1" := by decide
  have q2_12 : ofString "fp_accel_params" ≠ ofString "bls_g1_accel_p2" := by decide
  have q2_13 : ofString "fp_accel_params" ≠ ofString "bls_discount" := by decide
  have q3_0 : ofString "fp_accel_a" ≠ ofString "heap_ptr" := by decide
  have q3_1 : ofString "fp_accel_a" ≠ ofString "bls_c" := by decide
  have q3_2 : ofString "fp_accel_a" ≠ ofString "fp_accel_params" := by decide
  have q3_4 : ofString "fp_accel_a" ≠ ofString "fp_accel_b" := by decide
  have q3_5 : ofString "fp_accel_a" ≠ ofString "fp_accel_zero" := by decide
  have q3_6 : ofString "fp_accel_a" ≠ ofString "fp_accel_d" := by decide
  have q3_7 : ofString "fp_accel_a" ≠ ofString "fp2_accel_params" := by decide
  have q3_8 : ofString "fp_accel_a" ≠ ofString "fp2_accel_f1" := by decide
  have q3_9 : ofString "fp_accel_a" ≠ ofString "fp2_accel_f2" := by decide
  have q3_10 : ofString "fp_accel_a" ≠ ofString "bls_g1_accel_params" := by decide
  have q3_11 : ofString "fp_accel_a" ≠ ofString "bls_g1_accel_p1" := by decide
  have q3_12 : ofString "fp_accel_a" ≠ ofString "bls_g1_accel_p2" := by decide
  have q3_13 : ofString "fp_accel_a" ≠ ofString "bls_discount" := by decide
  have q4_0 : ofString "fp_accel_b" ≠ ofString "heap_ptr" := by decide
  have q4_1 : ofString "fp_accel_b" ≠ ofString "bls_c" := by decide
  have q4_2 : ofString "fp_accel_b" ≠ ofString "fp_accel_params" := by decide
  have q4_3 : ofString "fp_accel_b" ≠ ofString "fp_accel_a" := by decide
  have q4_5 : ofString "fp_accel_b" ≠ ofString "fp_accel_zero" := by decide
  have q4_6 : ofString "fp_accel_b" ≠ ofString "fp_accel_d" := by decide
  have q4_7 : ofString "fp_accel_b" ≠ ofString "fp2_accel_params" := by decide
  have q4_8 : ofString "fp_accel_b" ≠ ofString "fp2_accel_f1" := by decide
  have q4_9 : ofString "fp_accel_b" ≠ ofString "fp2_accel_f2" := by decide
  have q4_10 : ofString "fp_accel_b" ≠ ofString "bls_g1_accel_params" := by decide
  have q4_11 : ofString "fp_accel_b" ≠ ofString "bls_g1_accel_p1" := by decide
  have q4_12 : ofString "fp_accel_b" ≠ ofString "bls_g1_accel_p2" := by decide
  have q4_13 : ofString "fp_accel_b" ≠ ofString "bls_discount" := by decide
  have q5_0 : ofString "fp_accel_zero" ≠ ofString "heap_ptr" := by decide
  have q5_1 : ofString "fp_accel_zero" ≠ ofString "bls_c" := by decide
  have q5_2 : ofString "fp_accel_zero" ≠ ofString "fp_accel_params" := by decide
  have q5_3 : ofString "fp_accel_zero" ≠ ofString "fp_accel_a" := by decide
  have q5_4 : ofString "fp_accel_zero" ≠ ofString "fp_accel_b" := by decide
  have q5_6 : ofString "fp_accel_zero" ≠ ofString "fp_accel_d" := by decide
  have q5_7 : ofString "fp_accel_zero" ≠ ofString "fp2_accel_params" := by decide
  have q5_8 : ofString "fp_accel_zero" ≠ ofString "fp2_accel_f1" := by decide
  have q5_9 : ofString "fp_accel_zero" ≠ ofString "fp2_accel_f2" := by decide
  have q5_10 : ofString "fp_accel_zero" ≠ ofString "bls_g1_accel_params" := by decide
  have q5_11 : ofString "fp_accel_zero" ≠ ofString "bls_g1_accel_p1" := by decide
  have q5_12 : ofString "fp_accel_zero" ≠ ofString "bls_g1_accel_p2" := by decide
  have q5_13 : ofString "fp_accel_zero" ≠ ofString "bls_discount" := by decide
  have q6_0 : ofString "fp_accel_d" ≠ ofString "heap_ptr" := by decide
  have q6_1 : ofString "fp_accel_d" ≠ ofString "bls_c" := by decide
  have q6_2 : ofString "fp_accel_d" ≠ ofString "fp_accel_params" := by decide
  have q6_3 : ofString "fp_accel_d" ≠ ofString "fp_accel_a" := by decide
  have q6_4 : ofString "fp_accel_d" ≠ ofString "fp_accel_b" := by decide
  have q6_5 : ofString "fp_accel_d" ≠ ofString "fp_accel_zero" := by decide
  have q6_7 : ofString "fp_accel_d" ≠ ofString "fp2_accel_params" := by decide
  have q6_8 : ofString "fp_accel_d" ≠ ofString "fp2_accel_f1" := by decide
  have q6_9 : ofString "fp_accel_d" ≠ ofString "fp2_accel_f2" := by decide
  have q6_10 : ofString "fp_accel_d" ≠ ofString "bls_g1_accel_params" := by decide
  have q6_11 : ofString "fp_accel_d" ≠ ofString "bls_g1_accel_p1" := by decide
  have q6_12 : ofString "fp_accel_d" ≠ ofString "bls_g1_accel_p2" := by decide
  have q6_13 : ofString "fp_accel_d" ≠ ofString "bls_discount" := by decide
  have q7_0 : ofString "fp2_accel_params" ≠ ofString "heap_ptr" := by decide
  have q7_1 : ofString "fp2_accel_params" ≠ ofString "bls_c" := by decide
  have q7_2 : ofString "fp2_accel_params" ≠ ofString "fp_accel_params" := by decide
  have q7_3 : ofString "fp2_accel_params" ≠ ofString "fp_accel_a" := by decide
  have q7_4 : ofString "fp2_accel_params" ≠ ofString "fp_accel_b" := by decide
  have q7_5 : ofString "fp2_accel_params" ≠ ofString "fp_accel_zero" := by decide
  have q7_6 : ofString "fp2_accel_params" ≠ ofString "fp_accel_d" := by decide
  have q7_8 : ofString "fp2_accel_params" ≠ ofString "fp2_accel_f1" := by decide
  have q7_9 : ofString "fp2_accel_params" ≠ ofString "fp2_accel_f2" := by decide
  have q7_10 : ofString "fp2_accel_params" ≠ ofString "bls_g1_accel_params" := by decide
  have q7_11 : ofString "fp2_accel_params" ≠ ofString "bls_g1_accel_p1" := by decide
  have q7_12 : ofString "fp2_accel_params" ≠ ofString "bls_g1_accel_p2" := by decide
  have q7_13 : ofString "fp2_accel_params" ≠ ofString "bls_discount" := by decide
  have q8_0 : ofString "fp2_accel_f1" ≠ ofString "heap_ptr" := by decide
  have q8_1 : ofString "fp2_accel_f1" ≠ ofString "bls_c" := by decide
  have q8_2 : ofString "fp2_accel_f1" ≠ ofString "fp_accel_params" := by decide
  have q8_3 : ofString "fp2_accel_f1" ≠ ofString "fp_accel_a" := by decide
  have q8_4 : ofString "fp2_accel_f1" ≠ ofString "fp_accel_b" := by decide
  have q8_5 : ofString "fp2_accel_f1" ≠ ofString "fp_accel_zero" := by decide
  have q8_6 : ofString "fp2_accel_f1" ≠ ofString "fp_accel_d" := by decide
  have q8_7 : ofString "fp2_accel_f1" ≠ ofString "fp2_accel_params" := by decide
  have q8_9 : ofString "fp2_accel_f1" ≠ ofString "fp2_accel_f2" := by decide
  have q8_10 : ofString "fp2_accel_f1" ≠ ofString "bls_g1_accel_params" := by decide
  have q8_11 : ofString "fp2_accel_f1" ≠ ofString "bls_g1_accel_p1" := by decide
  have q8_12 : ofString "fp2_accel_f1" ≠ ofString "bls_g1_accel_p2" := by decide
  have q8_13 : ofString "fp2_accel_f1" ≠ ofString "bls_discount" := by decide
  have q9_0 : ofString "fp2_accel_f2" ≠ ofString "heap_ptr" := by decide
  have q9_1 : ofString "fp2_accel_f2" ≠ ofString "bls_c" := by decide
  have q9_2 : ofString "fp2_accel_f2" ≠ ofString "fp_accel_params" := by decide
  have q9_3 : ofString "fp2_accel_f2" ≠ ofString "fp_accel_a" := by decide
  have q9_4 : ofString "fp2_accel_f2" ≠ ofString "fp_accel_b" := by decide
  have q9_5 : ofString "fp2_accel_f2" ≠ ofString "fp_accel_zero" := by decide
  have q9_6 : ofString "fp2_accel_f2" ≠ ofString "fp_accel_d" := by decide
  have q9_7 : ofString "fp2_accel_f2" ≠ ofString "fp2_accel_params" := by decide
  have q9_8 : ofString "fp2_accel_f2" ≠ ofString "fp2_accel_f1" := by decide
  have q9_10 : ofString "fp2_accel_f2" ≠ ofString "bls_g1_accel_params" := by decide
  have q9_11 : ofString "fp2_accel_f2" ≠ ofString "bls_g1_accel_p1" := by decide
  have q9_12 : ofString "fp2_accel_f2" ≠ ofString "bls_g1_accel_p2" := by decide
  have q9_13 : ofString "fp2_accel_f2" ≠ ofString "bls_discount" := by decide
  have q10_0 : ofString "bls_g1_accel_params" ≠ ofString "heap_ptr" := by decide
  have q10_1 : ofString "bls_g1_accel_params" ≠ ofString "bls_c" := by decide
  have q10_2 : ofString "bls_g1_accel_params" ≠ ofString "fp_accel_params" := by decide
  have q10_3 : ofString "bls_g1_accel_params" ≠ ofString "fp_accel_a" := by decide
  have q10_4 : ofString "bls_g1_accel_params" ≠ ofString "fp_accel_b" := by decide
  have q10_5 : ofString "bls_g1_accel_params" ≠ ofString "fp_accel_zero" := by decide
  have q10_6 : ofString "bls_g1_accel_params" ≠ ofString "fp_accel_d" := by decide
  have q10_7 : ofString "bls_g1_accel_params" ≠ ofString "fp2_accel_params" := by decide
  have q10_8 : ofString "bls_g1_accel_params" ≠ ofString "fp2_accel_f1" := by decide
  have q10_9 : ofString "bls_g1_accel_params" ≠ ofString "fp2_accel_f2" := by decide
  have q10_11 : ofString "bls_g1_accel_params" ≠ ofString "bls_g1_accel_p1" := by decide
  have q10_12 : ofString "bls_g1_accel_params" ≠ ofString "bls_g1_accel_p2" := by decide
  have q10_13 : ofString "bls_g1_accel_params" ≠ ofString "bls_discount" := by decide
  have q11_0 : ofString "bls_g1_accel_p1" ≠ ofString "heap_ptr" := by decide
  have q11_1 : ofString "bls_g1_accel_p1" ≠ ofString "bls_c" := by decide
  have q11_2 : ofString "bls_g1_accel_p1" ≠ ofString "fp_accel_params" := by decide
  have q11_3 : ofString "bls_g1_accel_p1" ≠ ofString "fp_accel_a" := by decide
  have q11_4 : ofString "bls_g1_accel_p1" ≠ ofString "fp_accel_b" := by decide
  have q11_5 : ofString "bls_g1_accel_p1" ≠ ofString "fp_accel_zero" := by decide
  have q11_6 : ofString "bls_g1_accel_p1" ≠ ofString "fp_accel_d" := by decide
  have q11_7 : ofString "bls_g1_accel_p1" ≠ ofString "fp2_accel_params" := by decide
  have q11_8 : ofString "bls_g1_accel_p1" ≠ ofString "fp2_accel_f1" := by decide
  have q11_9 : ofString "bls_g1_accel_p1" ≠ ofString "fp2_accel_f2" := by decide
  have q11_10 : ofString "bls_g1_accel_p1" ≠ ofString "bls_g1_accel_params" := by decide
  have q11_12 : ofString "bls_g1_accel_p1" ≠ ofString "bls_g1_accel_p2" := by decide
  have q11_13 : ofString "bls_g1_accel_p1" ≠ ofString "bls_discount" := by decide
  have q12_0 : ofString "bls_g1_accel_p2" ≠ ofString "heap_ptr" := by decide
  have q12_1 : ofString "bls_g1_accel_p2" ≠ ofString "bls_c" := by decide
  have q12_2 : ofString "bls_g1_accel_p2" ≠ ofString "fp_accel_params" := by decide
  have q12_3 : ofString "bls_g1_accel_p2" ≠ ofString "fp_accel_a" := by decide
  have q12_4 : ofString "bls_g1_accel_p2" ≠ ofString "fp_accel_b" := by decide
  have q12_5 : ofString "bls_g1_accel_p2" ≠ ofString "fp_accel_zero" := by decide
  have q12_6 : ofString "bls_g1_accel_p2" ≠ ofString "fp_accel_d" := by decide
  have q12_7 : ofString "bls_g1_accel_p2" ≠ ofString "fp2_accel_params" := by decide
  have q12_8 : ofString "bls_g1_accel_p2" ≠ ofString "fp2_accel_f1" := by decide
  have q12_9 : ofString "bls_g1_accel_p2" ≠ ofString "fp2_accel_f2" := by decide
  have q12_10 : ofString "bls_g1_accel_p2" ≠ ofString "bls_g1_accel_params" := by decide
  have q12_11 : ofString "bls_g1_accel_p2" ≠ ofString "bls_g1_accel_p1" := by decide
  have q12_13 : ofString "bls_g1_accel_p2" ≠ ofString "bls_discount" := by decide
  have q13_0 : ofString "bls_discount" ≠ ofString "heap_ptr" := by decide
  have q13_1 : ofString "bls_discount" ≠ ofString "bls_c" := by decide
  have q13_2 : ofString "bls_discount" ≠ ofString "fp_accel_params" := by decide
  have q13_3 : ofString "bls_discount" ≠ ofString "fp_accel_a" := by decide
  have q13_4 : ofString "bls_discount" ≠ ofString "fp_accel_b" := by decide
  have q13_5 : ofString "bls_discount" ≠ ofString "fp_accel_zero" := by decide
  have q13_6 : ofString "bls_discount" ≠ ofString "fp_accel_d" := by decide
  have q13_7 : ofString "bls_discount" ≠ ofString "fp2_accel_params" := by decide
  have q13_8 : ofString "bls_discount" ≠ ofString "fp2_accel_f1" := by decide
  have q13_9 : ofString "bls_discount" ≠ ofString "fp2_accel_f2" := by decide
  have q13_10 : ofString "bls_discount" ≠ ofString "bls_g1_accel_params" := by decide
  have q13_11 : ofString "bls_discount" ≠ ofString "bls_g1_accel_p1" := by decide
  have q13_12 : ofString "bls_discount" ≠ ofString "bls_g1_accel_p2" := by decide
  let E := callEntryStateHOLFinite state HolFiniteMapExact.empty
  have guard : evaluateHOLFiniteState E
      (.ite (.cmp .notEqual (.var .global (ofString "bls_discount")) (.const 0)) (.return (.const 0)) .skip) = (none,E) := by
    rw [evaluateHOLFiniteState_ite]
    simp [E,callEntryStateHOLFinite,evalHOLExact,discountZero,Compiler.Encoders.Asm.wordCmpHOL,evaluateHOLFiniteState_skip]
  obtain ⟨t1,c1,b1,b1',l1,o1,d1,g1⟩ := evaluate_blsLibInit_call_first E H code heap aligned positive room
    constsZero fpZero fp2Zero g1Zero words arena (by change 112 ≤ state.clock - 1; omega)
  have t7760 : (H + 7568 + 192).toNat = H.toNat + 7760 := by simp [BitVec.toNat_add] <;> omega
  obtain ⟨req,fin,_,_⟩ := allocation_success_bounds (H + 7568 + 192) 2048 (by rw [t7760]; simp; omega)
  obtain ⟨r1,a1,c2,_,_,k2,d2,_,n2,h2,o2⟩ := evaluate_alloc_global_call t1 (.panop .mul [.const 256,.const 8]) (H + 7568 + 192) 2048 0
    (ofString "bls_discount") (by simp [evalListHOLFinite,evalListHOLExact,evalHOLExact,panOpHOL,valueIsWord,valueWord])
    (o1.trans code) (by change state.clock - 1 ≤ t1.clock + 112 at b1; omega) (by rw [g1]; simp [*,E,callEntryStateHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,blsLibGlobals,fpAccelGlobals,fp2AccelInitGlobals,blsG1AccelInitGlobals])
    (by rw [g1]; simp [*,E,callEntryStateHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,blsLibGlobals,fpAccelGlobals,fp2AccelInitGlobals,blsG1AccelInitGlobals]) (by decide) req fin
  have finish := allocationEnd_aligned_exact (H + 7568 + 192) 2048 (by rw [t7760]; omega) (by decide) (by rw [t7760]; simp; omega)
  rw [finish] at h2
  have g2 := alloc_globals_eq t1 r1 _ _ _ (by decide) n2 h2 o2
  have hd : r1.globals.lookup (ofString "bls_discount") = some (.val (.word (H + 7568 + 192))) := n2
  have stores := evaluate_globalConstantStores r1 (ofString "bls_discount") (H + 7568 + 192) blsDiscountCells (.return (.const 0)) hd
    (by
      intro cell member
      have bound := blsDiscountCells_offset cell member
      rw [d2,d1]
      apply arena
      · rw [BitVec.toNat_add_of_lt (by rw [t7760]; omega),t7760]; omega
      · rw [BitVec.toNat_add_of_lt (by rw [t7760]; omega),t7760]; omega)
  have body : evaluateHOLFiniteState E (sourceFunctionBody Guest.guestFn_bls_precompiles_init) =
      (some (.returned (.val (.word 0))),emptyLocalsHOLFinite {r1 with memory := memWrites r1.memory (H + 7568 + 192) blsDiscountCells}) := by
    rw [source_blsPrecompilesInit_body,bnSeqNone guard,bnSeqNone c1,bnSeqNone a1,stores]
    simp [evaluateHOLFiniteState_return,evalHOLExact,shapeOfHOLExact]
  have lookup := pan_no_args_lookup state.code.lookup (ofString "bls_precompiles_init")
    (sourceFunctionBody Guest.guestFn_bls_precompiles_init) (by rw [code]; exact originalRuntimeCode_blsPrecompilesInit_lookup)
  have call := evaluateHOLFiniteState_call_return_caller_locals state none (ofString "bls_precompiles_init") [] []
    (sourceFunctionBody Guest.guestFn_bls_precompiles_init) HolFiniteMapExact.empty .one (.val (.word 0)) _
    rfl lookup (by omega) body (by simp [shapeOfHOLExact,shapeEqHOL])
  refine ⟨_,call,?_,?_,rfl,k2.trans o1,d2.trans d1,?_⟩
  · change state.clock ≤ r1.clock + 114
    rw [c2]
    change state.clock - 1 ≤ t1.clock + 112 at b1
    omega
  · change r1.clock ≤ state.clock
    rw [c2]
    change t1.clock ≤ state.clock - 1 at b1'
    omega
  · change r1.globals = _
    rw [g2,g1]
    simp only [blsInitGlobals,BitVec.add_assoc,BitVec.reduceAdd]
    rfl

#print axioms evaluate_blsPrecompilesInit_call_first

theorem blsInit_actual_end : (2713719944 : BitVec 64) + 9808 = 2713729752 := by decide

/-- First bls_precompiles_init at the actual entry heap 2713719944 left by the
first eight main initializers: final heap_ptr 2713729752. -/
theorem evaluate_blsPrecompilesInit_call_at_entry_heap {F : Type} (state : PanSemStateFiniteExact 64 F)
    (code : state.code = originalRuntimeCode)
    (heap : state.globals.lookup (ofString "heap_ptr") = some (.val (.word 2713719944)))
    (discountZero : state.globals.lookup (ofString "bls_discount") = some (.val (.word 0)))
    (constsZero : state.globals.lookup (ofString "bls_c") = some (.val (.word 0)))
    (fpZero : state.globals.lookup (ofString "fp_accel_params") = some (.val (.word 0)))
    (fp2Zero : state.globals.lookup (ofString "fp2_accel_params") = some (.val (.word 0)))
    (g1Zero : state.globals.lookup (ofString "bls_g1_accel_params") = some (.val (.word 0)))
    (words : ∀ name ∈ blsLibWordNames, ∃ word : BitVec 64, state.globals.lookup name = some (.val (.word word)))
    (arena : ∀ address : BitVec 64, 2713719944 ≤ address.toNat → address.toNat < 33806089496 → state.memaddrs address)
    (budget : 114 ≤ state.clock) :
    ∃ post : PanSemStateFiniteExact 64 F,
      evaluateHOLFiniteState state (.call (some (none,none)) (ofString "bls_precompiles_init") []) = (none,post) ∧
      state.clock ≤ post.clock + 114 ∧ post.clock ≤ state.clock ∧ post.locals = state.locals ∧
      post.code = state.code ∧ post.memaddrs = state.memaddrs ∧ post.globals = blsInitGlobals state.globals 2713719944 ∧
      post.globals.lookup (ofString "heap_ptr") = some (.val (.word 2713729752)) := by
  obtain ⟨post,run,b1,b2,l,c,d,g⟩ := evaluate_blsPrecompilesInit_call_first state 2713719944 code heap (by decide) (by decide)
    (by decide) discountZero constsZero fpZero fp2Zero g1Zero words (fun a lo hi => arena a (by simpa using lo) hi) budget
  refine ⟨post,run,b1,b2,l,c,d,g,?_⟩
  have e : ofString "bls_discount" ≠ ofString "heap_ptr" := by decide
  rw [g]
  simp [blsInitGlobals,HolFiniteMapExact.lookup_update,FUPDATE,e]

#print axioms evaluate_blsPrecompilesInit_call_at_entry_heap
end InitECandidate.Runtime
