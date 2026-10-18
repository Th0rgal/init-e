import InitECandidate.Runtime.BlsPairAccelInitSuccess
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

/-- Globals after the first bls_lib_init from aligned heap H. -/
def blsLibGlobals (g : HolFiniteMapExact MlS (ValueHOL 64)) (H : BitVec 64) : HolFiniteMapExact MlS (ValueHOL 64) :=
  blsG1AccelInitGlobals (fp2AccelInitGlobals (fpAccelGlobals
    ((g.update (ofString "heap_ptr",.val (.word (H + 7136)))).update (ofString "bls_c",.val (.word H)))
    (H + 7136)) (H + 7376)) (H + 7568)

def blsLibWordNames : List MlS :=
  [ofString "fp_accel_a",ofString "fp_accel_b",ofString "fp_accel_zero",ofString "fp_accel_d",
   ofString "fp2_accel_f1",ofString "fp2_accel_f2",ofString "bls_g1_accel_p1",ofString "bls_g1_accel_p2"]

theorem evaluate_blsLibInit_call_first {F : Type} (state : PanSemStateFiniteExact 64 F) (H : BitVec 64)
    (code : state.code = originalRuntimeCode)
    (heap : state.globals.lookup (ofString "heap_ptr") = some (.val (.word H)))
    (aligned : H.toNat % 8 = 0) (positive : 0 < H.toNat) (room : H.toNat + 12000 ≤ 33806089496)
    (constsZero : state.globals.lookup (ofString "bls_c") = some (.val (.word 0)))
    (fpZero : state.globals.lookup (ofString "fp_accel_params") = some (.val (.word 0)))
    (fp2Zero : state.globals.lookup (ofString "fp2_accel_params") = some (.val (.word 0)))
    (g1Zero : state.globals.lookup (ofString "bls_g1_accel_params") = some (.val (.word 0)))
    (words : ∀ name ∈ blsLibWordNames, ∃ word : BitVec 64, state.globals.lookup name = some (.val (.word word)))
    (arena : ∀ address : BitVec 64, H.toNat ≤ address.toNat → address.toNat < 33806089496 → state.memaddrs address)
    (budget : 112 ≤ state.clock) :
    ∃ post : PanSemStateFiniteExact 64 F,
      evaluateHOLFiniteState state (.call (some (none,none)) (ofString "bls_lib_init") []) = (none,post) ∧
      state.clock ≤ post.clock + 112 ∧ post.clock ≤ state.clock ∧ post.locals = state.locals ∧
      post.code = state.code ∧ post.memaddrs = state.memaddrs ∧ post.globals = blsLibGlobals state.globals H := by
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
  have w := fun n (h : n ∈ blsLibWordNames) => words n h
  have add : ∀ k : Nat, k ≤ 12000 → (H + BitVec.ofNat 64 k).toNat = H.toNat + k := by
    intro k hk; rw [BitVec.toNat_add_of_lt (by simp; omega)]; simp; omega
  let E := callEntryStateHOLFinite state HolFiniteMapExact.empty
  obtain ⟨t1,c1,k1,l1,o1,d1,m1,g1⟩ := evaluate_blsConstsInit_call_first E H code heap aligned (by omega) constsZero arena
    (by change 2 ≤ state.clock - 1; omega)
  have t7136 := add 7136 (by omega)
  obtain ⟨t2,c2,b2,b2',l2,o2,d2,g2⟩ := evaluate_fpAccelInit_call_first t1 H (H + 7136) (o1.trans code)
    (by rw [g1]; simp [*,E,callEntryStateHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]) (by rw [g1]; simp [*,E,callEntryStateHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE])
    (by intro e; subst e; simp at positive) aligned (by simpa [t7136] using (show (H.toNat + 7136) % 8 = 0 by omega))
    (by simpa [t7136] using (show H.toNat + 96 ≤ H.toNat + 7136 by omega)) (by simpa [t7136] using (show H.toNat + 7136 + 2048 ≤ 33806089496 by omega))
    (by rw [g1]; simp [*,E,callEntryStateHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE])
    (by intro n m; rw [g1]; simp only [List.mem_cons,List.not_mem_nil,or_false] at m
        rcases m with rfl|rfl|rfl|rfl <;> simp [*,E,callEntryStateHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE] <;> exact w _ (by simp [blsLibWordNames]))
    (by intro a lo hi; rw [d1]; exact arena a lo hi) (by rw [k1]; change 102 ≤ state.clock - 1 - 2; omega)
  have t7376 : (H + 7136 + 240).toNat = H.toNat + 7376 := by simp [BitVec.toNat_add] <;> omega
  have t7568 : (H + 7136 + 240 + 192).toNat = H.toNat + 7568 := by simp [BitVec.toNat_add] <;> omega
  obtain ⟨t3,c3,k3,l3,o3,d3,g3⟩ := evaluate_fp2AccelInit_call_first t2 H (H + 7136 + 240) (o2.trans (o1.trans code))
    (by rw [g2,g1]; simp [*,E,callEntryStateHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,fpAccelGlobals,fp2AccelInitGlobals]) (by rw [g2,g1]; simp [*,E,callEntryStateHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,fpAccelGlobals,fp2AccelInitGlobals]) (by intro e; subst e; simp at positive)
    (by rw [t7376]; omega) (by rw [t7376]; omega) (by rw [g2,g1]; simp [*,E,callEntryStateHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,fpAccelGlobals,fp2AccelInitGlobals])
    (by rw [g2,g1]; simp [*,E,callEntryStateHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,fpAccelGlobals,fp2AccelInitGlobals]; exact w _ (by simp [blsLibWordNames])) (by rw [g2,g1]; simp [*,E,callEntryStateHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,fpAccelGlobals,fp2AccelInitGlobals]; exact w _ (by simp [blsLibWordNames]))
    (by rw [k1] at b2; change 4 ≤ t2.clock; change state.clock - 1 - 2 ≤ t2.clock + 102 at b2; omega)
  obtain ⟨t4,c4,k4,l4,o4,d4,g4⟩ := evaluate_blsG1AccelInit_call_first t3 H (H + 7136 + 240 + 192) (o3.trans (o2.trans (o1.trans code)))
    (by rw [g3,g2,g1]; simp [*,E,callEntryStateHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,fpAccelGlobals,fp2AccelInitGlobals]) (by rw [g3,g2,g1]; simp [*,E,callEntryStateHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,fpAccelGlobals,fp2AccelInitGlobals]) (by intro e; subst e; simp at positive)
    (by rw [t7568]; omega) (by rw [t7568]; omega) (by rw [g3,g2,g1]; simp [*,E,callEntryStateHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,fpAccelGlobals,fp2AccelInitGlobals])
    (by rw [g3,g2,g1]; simp [*,E,callEntryStateHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,fpAccelGlobals,fp2AccelInitGlobals]; exact w _ (by simp [blsLibWordNames])) (by rw [g3,g2,g1]; simp [*,E,callEntryStateHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,fpAccelGlobals,fp2AccelInitGlobals]; exact w _ (by simp [blsLibWordNames]))
    (by rw [k3]; rw [k1] at b2; change state.clock - 1 - 2 ≤ t2.clock + 102 at b2; omega)
  have body : evaluateHOLFiniteState E (sourceFunctionBody Guest.guestFn_bls_lib_init) =
      (some (.returned (.val (.word 0))),emptyLocalsHOLFinite t4) := by
    rw [source_blsLibInit_body,bnSeqNone c1,bnSeqNone c2,bnSeqNone c3,bnSeqNone c4]
    simp [evaluateHOLFiniteState_return,evalHOLExact,shapeOfHOLExact]
  have lookup := pan_no_args_lookup state.code.lookup (ofString "bls_lib_init")
    (sourceFunctionBody Guest.guestFn_bls_lib_init) (by rw [code]; exact originalRuntimeCode_blsLibInit_lookup)
  have call := evaluateHOLFiniteState_call_return_caller_locals state none (ofString "bls_lib_init") [] []
    (sourceFunctionBody Guest.guestFn_bls_lib_init) HolFiniteMapExact.empty .one (.val (.word 0)) _
    rfl lookup (by omega) body (by simp [shapeOfHOLExact,shapeEqHOL])
  refine ⟨_,call,?_,?_,rfl,o4.trans (o3.trans (o2.trans o1)),d4.trans (d3.trans (d2.trans d1)),?_⟩
  · change state.clock ≤ t4.clock + 112
    rw [k1] at b2
    change state.clock - 1 - 2 ≤ t2.clock + 102 at b2
    omega
  · change t4.clock ≤ state.clock
    rw [k1] at b2'
    change t2.clock ≤ state.clock - 1 - 2 at b2'
    omega
  · change t4.globals = _
    rw [g4,g3,g2,g1]
    simp only [blsLibGlobals,BitVec.add_assoc,BitVec.reduceAdd]
    rfl

#print axioms evaluate_blsLibInit_call_first
end InitECandidate.Runtime
