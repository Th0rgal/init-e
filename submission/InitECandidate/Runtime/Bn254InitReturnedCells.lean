import InitECandidate.Runtime.Bn254InitReturned
import InitECandidate.Runtime.Bn254AccelInitSuccessCells
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
theorem bn254Init_body_returned_cells {F : Type} (state post : PanSemStateFiniteExact 64 F) (H : BitVec 64)
    (v : ValueHOL 64) (code : state.code = originalRuntimeCode)
    (heap : state.globals.lookup (ofString "heap_ptr") = some (.val (.word H)))
    (aligned : H.toNat % 8 = 0) (positive : 0 < H.toNat) (room : H.toNat + 2048 ≤ 33806089496)
    (gammaZero : state.globals.lookup (ofString "bn_gamma") = some (.val (.word 0)))
    (paramsZero : state.globals.lookup (ofString "bn_accel_params") = some (.val (.word 0)))
    (words : ∀ name ∈ bn254AccelNames, ∃ word : BitVec 64, state.globals.lookup name = some (.val (.word word)))
    (b2Word : ∃ word : BitVec 64, state.globals.lookup (ofString "bn_b2") = some (.val (.word word)))
    (expwWord : ∃ word : BitVec 64, state.globals.lookup (ofString "bn_expw") = some (.val (.word word)))
    (arena : ∀ address : BitVec 64, address.toNat % 8 = 0 → H.toNat ≤ address.toNat → address.toNat < 33806089496 → state.memaddrs address)
    (budget : 4 ≤ state.clock)
    (run : evaluateHOLFiniteState state (sourceFunctionBody Guest.guestFn_bn254_init) = (some (.returned v),post)) :
    v = .val (.word 0) ∧ post.globals = bn254InitGlobals state.globals H := by
  have q0_1 : ofString "heap_ptr" ≠ ofString "bn_accel_params" := by decide
  have q0_2 : ofString "heap_ptr" ≠ ofString "bn_accel_a" := by decide
  have q0_3 : ofString "heap_ptr" ≠ ofString "bn_accel_b" := by decide
  have q0_4 : ofString "heap_ptr" ≠ ofString "bn_accel_zero" := by decide
  have q0_5 : ofString "heap_ptr" ≠ ofString "bn_accel_m" := by decide
  have q0_6 : ofString "heap_ptr" ≠ ofString "bn_accel_d" := by decide
  have q0_7 : ofString "heap_ptr" ≠ ofString "bn_accel_fp2_params" := by decide
  have q0_8 : ofString "heap_ptr" ≠ ofString "bn_accel_fp2_f1" := by decide
  have q0_9 : ofString "heap_ptr" ≠ ofString "bn_accel_fp2_f2" := by decide
  have q0_10 : ofString "heap_ptr" ≠ ofString "bn_accel_g1_params" := by decide
  have q0_11 : ofString "heap_ptr" ≠ ofString "bn_accel_g1_p1" := by decide
  have q0_12 : ofString "heap_ptr" ≠ ofString "bn_accel_g1_p2" := by decide
  have q0_13 : ofString "heap_ptr" ≠ ofString "bn_gamma" := by decide
  have q0_14 : ofString "heap_ptr" ≠ ofString "bn_b2" := by decide
  have q0_15 : ofString "heap_ptr" ≠ ofString "bn_expw" := by decide
  have q1_0 : ofString "bn_accel_params" ≠ ofString "heap_ptr" := by decide
  have q1_2 : ofString "bn_accel_params" ≠ ofString "bn_accel_a" := by decide
  have q1_3 : ofString "bn_accel_params" ≠ ofString "bn_accel_b" := by decide
  have q1_4 : ofString "bn_accel_params" ≠ ofString "bn_accel_zero" := by decide
  have q1_5 : ofString "bn_accel_params" ≠ ofString "bn_accel_m" := by decide
  have q1_6 : ofString "bn_accel_params" ≠ ofString "bn_accel_d" := by decide
  have q1_7 : ofString "bn_accel_params" ≠ ofString "bn_accel_fp2_params" := by decide
  have q1_8 : ofString "bn_accel_params" ≠ ofString "bn_accel_fp2_f1" := by decide
  have q1_9 : ofString "bn_accel_params" ≠ ofString "bn_accel_fp2_f2" := by decide
  have q1_10 : ofString "bn_accel_params" ≠ ofString "bn_accel_g1_params" := by decide
  have q1_11 : ofString "bn_accel_params" ≠ ofString "bn_accel_g1_p1" := by decide
  have q1_12 : ofString "bn_accel_params" ≠ ofString "bn_accel_g1_p2" := by decide
  have q1_13 : ofString "bn_accel_params" ≠ ofString "bn_gamma" := by decide
  have q1_14 : ofString "bn_accel_params" ≠ ofString "bn_b2" := by decide
  have q1_15 : ofString "bn_accel_params" ≠ ofString "bn_expw" := by decide
  have q2_0 : ofString "bn_accel_a" ≠ ofString "heap_ptr" := by decide
  have q2_1 : ofString "bn_accel_a" ≠ ofString "bn_accel_params" := by decide
  have q2_3 : ofString "bn_accel_a" ≠ ofString "bn_accel_b" := by decide
  have q2_4 : ofString "bn_accel_a" ≠ ofString "bn_accel_zero" := by decide
  have q2_5 : ofString "bn_accel_a" ≠ ofString "bn_accel_m" := by decide
  have q2_6 : ofString "bn_accel_a" ≠ ofString "bn_accel_d" := by decide
  have q2_7 : ofString "bn_accel_a" ≠ ofString "bn_accel_fp2_params" := by decide
  have q2_8 : ofString "bn_accel_a" ≠ ofString "bn_accel_fp2_f1" := by decide
  have q2_9 : ofString "bn_accel_a" ≠ ofString "bn_accel_fp2_f2" := by decide
  have q2_10 : ofString "bn_accel_a" ≠ ofString "bn_accel_g1_params" := by decide
  have q2_11 : ofString "bn_accel_a" ≠ ofString "bn_accel_g1_p1" := by decide
  have q2_12 : ofString "bn_accel_a" ≠ ofString "bn_accel_g1_p2" := by decide
  have q2_13 : ofString "bn_accel_a" ≠ ofString "bn_gamma" := by decide
  have q2_14 : ofString "bn_accel_a" ≠ ofString "bn_b2" := by decide
  have q2_15 : ofString "bn_accel_a" ≠ ofString "bn_expw" := by decide
  have q3_0 : ofString "bn_accel_b" ≠ ofString "heap_ptr" := by decide
  have q3_1 : ofString "bn_accel_b" ≠ ofString "bn_accel_params" := by decide
  have q3_2 : ofString "bn_accel_b" ≠ ofString "bn_accel_a" := by decide
  have q3_4 : ofString "bn_accel_b" ≠ ofString "bn_accel_zero" := by decide
  have q3_5 : ofString "bn_accel_b" ≠ ofString "bn_accel_m" := by decide
  have q3_6 : ofString "bn_accel_b" ≠ ofString "bn_accel_d" := by decide
  have q3_7 : ofString "bn_accel_b" ≠ ofString "bn_accel_fp2_params" := by decide
  have q3_8 : ofString "bn_accel_b" ≠ ofString "bn_accel_fp2_f1" := by decide
  have q3_9 : ofString "bn_accel_b" ≠ ofString "bn_accel_fp2_f2" := by decide
  have q3_10 : ofString "bn_accel_b" ≠ ofString "bn_accel_g1_params" := by decide
  have q3_11 : ofString "bn_accel_b" ≠ ofString "bn_accel_g1_p1" := by decide
  have q3_12 : ofString "bn_accel_b" ≠ ofString "bn_accel_g1_p2" := by decide
  have q3_13 : ofString "bn_accel_b" ≠ ofString "bn_gamma" := by decide
  have q3_14 : ofString "bn_accel_b" ≠ ofString "bn_b2" := by decide
  have q3_15 : ofString "bn_accel_b" ≠ ofString "bn_expw" := by decide
  have q4_0 : ofString "bn_accel_zero" ≠ ofString "heap_ptr" := by decide
  have q4_1 : ofString "bn_accel_zero" ≠ ofString "bn_accel_params" := by decide
  have q4_2 : ofString "bn_accel_zero" ≠ ofString "bn_accel_a" := by decide
  have q4_3 : ofString "bn_accel_zero" ≠ ofString "bn_accel_b" := by decide
  have q4_5 : ofString "bn_accel_zero" ≠ ofString "bn_accel_m" := by decide
  have q4_6 : ofString "bn_accel_zero" ≠ ofString "bn_accel_d" := by decide
  have q4_7 : ofString "bn_accel_zero" ≠ ofString "bn_accel_fp2_params" := by decide
  have q4_8 : ofString "bn_accel_zero" ≠ ofString "bn_accel_fp2_f1" := by decide
  have q4_9 : ofString "bn_accel_zero" ≠ ofString "bn_accel_fp2_f2" := by decide
  have q4_10 : ofString "bn_accel_zero" ≠ ofString "bn_accel_g1_params" := by decide
  have q4_11 : ofString "bn_accel_zero" ≠ ofString "bn_accel_g1_p1" := by decide
  have q4_12 : ofString "bn_accel_zero" ≠ ofString "bn_accel_g1_p2" := by decide
  have q4_13 : ofString "bn_accel_zero" ≠ ofString "bn_gamma" := by decide
  have q4_14 : ofString "bn_accel_zero" ≠ ofString "bn_b2" := by decide
  have q4_15 : ofString "bn_accel_zero" ≠ ofString "bn_expw" := by decide
  have q5_0 : ofString "bn_accel_m" ≠ ofString "heap_ptr" := by decide
  have q5_1 : ofString "bn_accel_m" ≠ ofString "bn_accel_params" := by decide
  have q5_2 : ofString "bn_accel_m" ≠ ofString "bn_accel_a" := by decide
  have q5_3 : ofString "bn_accel_m" ≠ ofString "bn_accel_b" := by decide
  have q5_4 : ofString "bn_accel_m" ≠ ofString "bn_accel_zero" := by decide
  have q5_6 : ofString "bn_accel_m" ≠ ofString "bn_accel_d" := by decide
  have q5_7 : ofString "bn_accel_m" ≠ ofString "bn_accel_fp2_params" := by decide
  have q5_8 : ofString "bn_accel_m" ≠ ofString "bn_accel_fp2_f1" := by decide
  have q5_9 : ofString "bn_accel_m" ≠ ofString "bn_accel_fp2_f2" := by decide
  have q5_10 : ofString "bn_accel_m" ≠ ofString "bn_accel_g1_params" := by decide
  have q5_11 : ofString "bn_accel_m" ≠ ofString "bn_accel_g1_p1" := by decide
  have q5_12 : ofString "bn_accel_m" ≠ ofString "bn_accel_g1_p2" := by decide
  have q5_13 : ofString "bn_accel_m" ≠ ofString "bn_gamma" := by decide
  have q5_14 : ofString "bn_accel_m" ≠ ofString "bn_b2" := by decide
  have q5_15 : ofString "bn_accel_m" ≠ ofString "bn_expw" := by decide
  have q6_0 : ofString "bn_accel_d" ≠ ofString "heap_ptr" := by decide
  have q6_1 : ofString "bn_accel_d" ≠ ofString "bn_accel_params" := by decide
  have q6_2 : ofString "bn_accel_d" ≠ ofString "bn_accel_a" := by decide
  have q6_3 : ofString "bn_accel_d" ≠ ofString "bn_accel_b" := by decide
  have q6_4 : ofString "bn_accel_d" ≠ ofString "bn_accel_zero" := by decide
  have q6_5 : ofString "bn_accel_d" ≠ ofString "bn_accel_m" := by decide
  have q6_7 : ofString "bn_accel_d" ≠ ofString "bn_accel_fp2_params" := by decide
  have q6_8 : ofString "bn_accel_d" ≠ ofString "bn_accel_fp2_f1" := by decide
  have q6_9 : ofString "bn_accel_d" ≠ ofString "bn_accel_fp2_f2" := by decide
  have q6_10 : ofString "bn_accel_d" ≠ ofString "bn_accel_g1_params" := by decide
  have q6_11 : ofString "bn_accel_d" ≠ ofString "bn_accel_g1_p1" := by decide
  have q6_12 : ofString "bn_accel_d" ≠ ofString "bn_accel_g1_p2" := by decide
  have q6_13 : ofString "bn_accel_d" ≠ ofString "bn_gamma" := by decide
  have q6_14 : ofString "bn_accel_d" ≠ ofString "bn_b2" := by decide
  have q6_15 : ofString "bn_accel_d" ≠ ofString "bn_expw" := by decide
  have q7_0 : ofString "bn_accel_fp2_params" ≠ ofString "heap_ptr" := by decide
  have q7_1 : ofString "bn_accel_fp2_params" ≠ ofString "bn_accel_params" := by decide
  have q7_2 : ofString "bn_accel_fp2_params" ≠ ofString "bn_accel_a" := by decide
  have q7_3 : ofString "bn_accel_fp2_params" ≠ ofString "bn_accel_b" := by decide
  have q7_4 : ofString "bn_accel_fp2_params" ≠ ofString "bn_accel_zero" := by decide
  have q7_5 : ofString "bn_accel_fp2_params" ≠ ofString "bn_accel_m" := by decide
  have q7_6 : ofString "bn_accel_fp2_params" ≠ ofString "bn_accel_d" := by decide
  have q7_8 : ofString "bn_accel_fp2_params" ≠ ofString "bn_accel_fp2_f1" := by decide
  have q7_9 : ofString "bn_accel_fp2_params" ≠ ofString "bn_accel_fp2_f2" := by decide
  have q7_10 : ofString "bn_accel_fp2_params" ≠ ofString "bn_accel_g1_params" := by decide
  have q7_11 : ofString "bn_accel_fp2_params" ≠ ofString "bn_accel_g1_p1" := by decide
  have q7_12 : ofString "bn_accel_fp2_params" ≠ ofString "bn_accel_g1_p2" := by decide
  have q7_13 : ofString "bn_accel_fp2_params" ≠ ofString "bn_gamma" := by decide
  have q7_14 : ofString "bn_accel_fp2_params" ≠ ofString "bn_b2" := by decide
  have q7_15 : ofString "bn_accel_fp2_params" ≠ ofString "bn_expw" := by decide
  have q8_0 : ofString "bn_accel_fp2_f1" ≠ ofString "heap_ptr" := by decide
  have q8_1 : ofString "bn_accel_fp2_f1" ≠ ofString "bn_accel_params" := by decide
  have q8_2 : ofString "bn_accel_fp2_f1" ≠ ofString "bn_accel_a" := by decide
  have q8_3 : ofString "bn_accel_fp2_f1" ≠ ofString "bn_accel_b" := by decide
  have q8_4 : ofString "bn_accel_fp2_f1" ≠ ofString "bn_accel_zero" := by decide
  have q8_5 : ofString "bn_accel_fp2_f1" ≠ ofString "bn_accel_m" := by decide
  have q8_6 : ofString "bn_accel_fp2_f1" ≠ ofString "bn_accel_d" := by decide
  have q8_7 : ofString "bn_accel_fp2_f1" ≠ ofString "bn_accel_fp2_params" := by decide
  have q8_9 : ofString "bn_accel_fp2_f1" ≠ ofString "bn_accel_fp2_f2" := by decide
  have q8_10 : ofString "bn_accel_fp2_f1" ≠ ofString "bn_accel_g1_params" := by decide
  have q8_11 : ofString "bn_accel_fp2_f1" ≠ ofString "bn_accel_g1_p1" := by decide
  have q8_12 : ofString "bn_accel_fp2_f1" ≠ ofString "bn_accel_g1_p2" := by decide
  have q8_13 : ofString "bn_accel_fp2_f1" ≠ ofString "bn_gamma" := by decide
  have q8_14 : ofString "bn_accel_fp2_f1" ≠ ofString "bn_b2" := by decide
  have q8_15 : ofString "bn_accel_fp2_f1" ≠ ofString "bn_expw" := by decide
  have q9_0 : ofString "bn_accel_fp2_f2" ≠ ofString "heap_ptr" := by decide
  have q9_1 : ofString "bn_accel_fp2_f2" ≠ ofString "bn_accel_params" := by decide
  have q9_2 : ofString "bn_accel_fp2_f2" ≠ ofString "bn_accel_a" := by decide
  have q9_3 : ofString "bn_accel_fp2_f2" ≠ ofString "bn_accel_b" := by decide
  have q9_4 : ofString "bn_accel_fp2_f2" ≠ ofString "bn_accel_zero" := by decide
  have q9_5 : ofString "bn_accel_fp2_f2" ≠ ofString "bn_accel_m" := by decide
  have q9_6 : ofString "bn_accel_fp2_f2" ≠ ofString "bn_accel_d" := by decide
  have q9_7 : ofString "bn_accel_fp2_f2" ≠ ofString "bn_accel_fp2_params" := by decide
  have q9_8 : ofString "bn_accel_fp2_f2" ≠ ofString "bn_accel_fp2_f1" := by decide
  have q9_10 : ofString "bn_accel_fp2_f2" ≠ ofString "bn_accel_g1_params" := by decide
  have q9_11 : ofString "bn_accel_fp2_f2" ≠ ofString "bn_accel_g1_p1" := by decide
  have q9_12 : ofString "bn_accel_fp2_f2" ≠ ofString "bn_accel_g1_p2" := by decide
  have q9_13 : ofString "bn_accel_fp2_f2" ≠ ofString "bn_gamma" := by decide
  have q9_14 : ofString "bn_accel_fp2_f2" ≠ ofString "bn_b2" := by decide
  have q9_15 : ofString "bn_accel_fp2_f2" ≠ ofString "bn_expw" := by decide
  have q10_0 : ofString "bn_accel_g1_params" ≠ ofString "heap_ptr" := by decide
  have q10_1 : ofString "bn_accel_g1_params" ≠ ofString "bn_accel_params" := by decide
  have q10_2 : ofString "bn_accel_g1_params" ≠ ofString "bn_accel_a" := by decide
  have q10_3 : ofString "bn_accel_g1_params" ≠ ofString "bn_accel_b" := by decide
  have q10_4 : ofString "bn_accel_g1_params" ≠ ofString "bn_accel_zero" := by decide
  have q10_5 : ofString "bn_accel_g1_params" ≠ ofString "bn_accel_m" := by decide
  have q10_6 : ofString "bn_accel_g1_params" ≠ ofString "bn_accel_d" := by decide
  have q10_7 : ofString "bn_accel_g1_params" ≠ ofString "bn_accel_fp2_params" := by decide
  have q10_8 : ofString "bn_accel_g1_params" ≠ ofString "bn_accel_fp2_f1" := by decide
  have q10_9 : ofString "bn_accel_g1_params" ≠ ofString "bn_accel_fp2_f2" := by decide
  have q10_11 : ofString "bn_accel_g1_params" ≠ ofString "bn_accel_g1_p1" := by decide
  have q10_12 : ofString "bn_accel_g1_params" ≠ ofString "bn_accel_g1_p2" := by decide
  have q10_13 : ofString "bn_accel_g1_params" ≠ ofString "bn_gamma" := by decide
  have q10_14 : ofString "bn_accel_g1_params" ≠ ofString "bn_b2" := by decide
  have q10_15 : ofString "bn_accel_g1_params" ≠ ofString "bn_expw" := by decide
  have q11_0 : ofString "bn_accel_g1_p1" ≠ ofString "heap_ptr" := by decide
  have q11_1 : ofString "bn_accel_g1_p1" ≠ ofString "bn_accel_params" := by decide
  have q11_2 : ofString "bn_accel_g1_p1" ≠ ofString "bn_accel_a" := by decide
  have q11_3 : ofString "bn_accel_g1_p1" ≠ ofString "bn_accel_b" := by decide
  have q11_4 : ofString "bn_accel_g1_p1" ≠ ofString "bn_accel_zero" := by decide
  have q11_5 : ofString "bn_accel_g1_p1" ≠ ofString "bn_accel_m" := by decide
  have q11_6 : ofString "bn_accel_g1_p1" ≠ ofString "bn_accel_d" := by decide
  have q11_7 : ofString "bn_accel_g1_p1" ≠ ofString "bn_accel_fp2_params" := by decide
  have q11_8 : ofString "bn_accel_g1_p1" ≠ ofString "bn_accel_fp2_f1" := by decide
  have q11_9 : ofString "bn_accel_g1_p1" ≠ ofString "bn_accel_fp2_f2" := by decide
  have q11_10 : ofString "bn_accel_g1_p1" ≠ ofString "bn_accel_g1_params" := by decide
  have q11_12 : ofString "bn_accel_g1_p1" ≠ ofString "bn_accel_g1_p2" := by decide
  have q11_13 : ofString "bn_accel_g1_p1" ≠ ofString "bn_gamma" := by decide
  have q11_14 : ofString "bn_accel_g1_p1" ≠ ofString "bn_b2" := by decide
  have q11_15 : ofString "bn_accel_g1_p1" ≠ ofString "bn_expw" := by decide
  have q12_0 : ofString "bn_accel_g1_p2" ≠ ofString "heap_ptr" := by decide
  have q12_1 : ofString "bn_accel_g1_p2" ≠ ofString "bn_accel_params" := by decide
  have q12_2 : ofString "bn_accel_g1_p2" ≠ ofString "bn_accel_a" := by decide
  have q12_3 : ofString "bn_accel_g1_p2" ≠ ofString "bn_accel_b" := by decide
  have q12_4 : ofString "bn_accel_g1_p2" ≠ ofString "bn_accel_zero" := by decide
  have q12_5 : ofString "bn_accel_g1_p2" ≠ ofString "bn_accel_m" := by decide
  have q12_6 : ofString "bn_accel_g1_p2" ≠ ofString "bn_accel_d" := by decide
  have q12_7 : ofString "bn_accel_g1_p2" ≠ ofString "bn_accel_fp2_params" := by decide
  have q12_8 : ofString "bn_accel_g1_p2" ≠ ofString "bn_accel_fp2_f1" := by decide
  have q12_9 : ofString "bn_accel_g1_p2" ≠ ofString "bn_accel_fp2_f2" := by decide
  have q12_10 : ofString "bn_accel_g1_p2" ≠ ofString "bn_accel_g1_params" := by decide
  have q12_11 : ofString "bn_accel_g1_p2" ≠ ofString "bn_accel_g1_p1" := by decide
  have q12_13 : ofString "bn_accel_g1_p2" ≠ ofString "bn_gamma" := by decide
  have q12_14 : ofString "bn_accel_g1_p2" ≠ ofString "bn_b2" := by decide
  have q12_15 : ofString "bn_accel_g1_p2" ≠ ofString "bn_expw" := by decide
  have q13_0 : ofString "bn_gamma" ≠ ofString "heap_ptr" := by decide
  have q13_1 : ofString "bn_gamma" ≠ ofString "bn_accel_params" := by decide
  have q13_2 : ofString "bn_gamma" ≠ ofString "bn_accel_a" := by decide
  have q13_3 : ofString "bn_gamma" ≠ ofString "bn_accel_b" := by decide
  have q13_4 : ofString "bn_gamma" ≠ ofString "bn_accel_zero" := by decide
  have q13_5 : ofString "bn_gamma" ≠ ofString "bn_accel_m" := by decide
  have q13_6 : ofString "bn_gamma" ≠ ofString "bn_accel_d" := by decide
  have q13_7 : ofString "bn_gamma" ≠ ofString "bn_accel_fp2_params" := by decide
  have q13_8 : ofString "bn_gamma" ≠ ofString "bn_accel_fp2_f1" := by decide
  have q13_9 : ofString "bn_gamma" ≠ ofString "bn_accel_fp2_f2" := by decide
  have q13_10 : ofString "bn_gamma" ≠ ofString "bn_accel_g1_params" := by decide
  have q13_11 : ofString "bn_gamma" ≠ ofString "bn_accel_g1_p1" := by decide
  have q13_12 : ofString "bn_gamma" ≠ ofString "bn_accel_g1_p2" := by decide
  have q13_14 : ofString "bn_gamma" ≠ ofString "bn_b2" := by decide
  have q13_15 : ofString "bn_gamma" ≠ ofString "bn_expw" := by decide
  have q14_0 : ofString "bn_b2" ≠ ofString "heap_ptr" := by decide
  have q14_1 : ofString "bn_b2" ≠ ofString "bn_accel_params" := by decide
  have q14_2 : ofString "bn_b2" ≠ ofString "bn_accel_a" := by decide
  have q14_3 : ofString "bn_b2" ≠ ofString "bn_accel_b" := by decide
  have q14_4 : ofString "bn_b2" ≠ ofString "bn_accel_zero" := by decide
  have q14_5 : ofString "bn_b2" ≠ ofString "bn_accel_m" := by decide
  have q14_6 : ofString "bn_b2" ≠ ofString "bn_accel_d" := by decide
  have q14_7 : ofString "bn_b2" ≠ ofString "bn_accel_fp2_params" := by decide
  have q14_8 : ofString "bn_b2" ≠ ofString "bn_accel_fp2_f1" := by decide
  have q14_9 : ofString "bn_b2" ≠ ofString "bn_accel_fp2_f2" := by decide
  have q14_10 : ofString "bn_b2" ≠ ofString "bn_accel_g1_params" := by decide
  have q14_11 : ofString "bn_b2" ≠ ofString "bn_accel_g1_p1" := by decide
  have q14_12 : ofString "bn_b2" ≠ ofString "bn_accel_g1_p2" := by decide
  have q14_13 : ofString "bn_b2" ≠ ofString "bn_gamma" := by decide
  have q14_15 : ofString "bn_b2" ≠ ofString "bn_expw" := by decide
  have q15_0 : ofString "bn_expw" ≠ ofString "heap_ptr" := by decide
  have q15_1 : ofString "bn_expw" ≠ ofString "bn_accel_params" := by decide
  have q15_2 : ofString "bn_expw" ≠ ofString "bn_accel_a" := by decide
  have q15_3 : ofString "bn_expw" ≠ ofString "bn_accel_b" := by decide
  have q15_4 : ofString "bn_expw" ≠ ofString "bn_accel_zero" := by decide
  have q15_5 : ofString "bn_expw" ≠ ofString "bn_accel_m" := by decide
  have q15_6 : ofString "bn_expw" ≠ ofString "bn_accel_d" := by decide
  have q15_7 : ofString "bn_expw" ≠ ofString "bn_accel_fp2_params" := by decide
  have q15_8 : ofString "bn_expw" ≠ ofString "bn_accel_fp2_f1" := by decide
  have q15_9 : ofString "bn_expw" ≠ ofString "bn_accel_fp2_f2" := by decide
  have q15_10 : ofString "bn_expw" ≠ ofString "bn_accel_g1_params" := by decide
  have q15_11 : ofString "bn_expw" ≠ ofString "bn_accel_g1_p1" := by decide
  have q15_12 : ofString "bn_expw" ≠ ofString "bn_accel_g1_p2" := by decide
  have q15_13 : ofString "bn_expw" ≠ ofString "bn_gamma" := by decide
  have q15_14 : ofString "bn_expw" ≠ ofString "bn_b2" := by decide
  obtain ⟨ob2,b2w⟩ := b2Word
  obtain ⟨oexp,expw⟩ := expwWord
  have small : ∀ k : Nat, k ≤ 2048 → (H + BitVec.ofNat 64 k).toNat = H.toNat + k := by
    intro k hk; rw [BitVec.toNat_add_of_lt (by simp; omega)]; simp; omega
  rw [source_bn254Init_body] at run
  have guard : evaluateHOLFiniteState state
      (.ite (.cmp .notEqual (.var .global (ofString "bn_gamma")) (.const 0)) (.return (.const 0)) .skip) = (none,state) := by
    rw [evaluateHOLFiniteState_ite]
    simp [evalHOLExact,gammaZero,Compiler.Encoders.Asm.wordCmpHOL,evaluateHOLFiniteState_skip]
  rw [bnSeqNone guard] at run
  -- first accelerator initialization through the actual call
  obtain ⟨bp,bodyRun,bclock,bcode,bdom,_,bglob⟩ := evaluate_bn254AccelInit_body_success_cells
    (callEntryStateHOLFinite state HolFiniteMapExact.empty) H code heap aligned room paramsZero words arena
    (by change 3 ≤ state.clock - 1; omega)
  have lookup := pan_no_args_lookup state.code.lookup (ofString "bn254_accel_init")
    (sourceFunctionBody Guest.guestFn_bn254_accel_init) (by rw [code]; exact originalRuntimeCode_bn254AccelInit_lookup)
  have accel := evaluateHOLFiniteState_call_return_caller_locals state none (ofString "bn254_accel_init") [] []
    (sourceFunctionBody Guest.guestFn_bn254_accel_init) HolFiniteMapExact.empty .one (.val (.word 0)) bp
    rfl lookup (by omega) bodyRun (by simp [shapeOfHOLExact,shapeEqHOL])
  rw [bnSeqNone accel] at run
  let s1 : PanSemStateFiniteExact 64 F := {bp with locals := state.locals}
  have s1g : s1.globals = bn254AccelGlobals state.globals H := bglob
  have s1c : s1.code = originalRuntimeCode := bcode.trans code
  have s1d : s1.memaddrs = state.memaddrs := bdom
  have notAccel : ∀ w, w ∈ [ofString "bn_gamma",ofString "bn_b2",ofString "bn_expw"] →
      (bn254AccelGlobals state.globals H).lookup w = state.globals.lookup w := by
    intro w m
    simp only [List.mem_cons,List.not_mem_nil,or_false] at m
    rcases m with rfl|rfl|rfl <;> simp [*,HolFiniteMapExact.lookup_update,FUPDATE,bn254AccelGlobals]
  have aligned416 : (H + 416).toNat % 8 = 0 := (by simp [BitVec.toNat_add] <;> omega)
  obtain ⟨req1,fin1,_,_⟩ := allocation_success_bounds (H + 416) 384 (by simp [BitVec.toNat_add] <;> omega)
  obtain ⟨r1,a1,_,_,_,k1,d1,_,n1,h1,o1⟩ := evaluate_alloc_global_call s1 (.panop .mul [.const 6,.const 64]) (H + 416) 384 0
    (ofString "bn_gamma") (by simp [evalListHOLFinite,evalListHOLExact,evalHOLExact,panOpHOL,valueIsWord,valueWord])
    s1c (call_seq_returned_clock run) (by rw [s1g]; simp [*,HolFiniteMapExact.lookup_update,FUPDATE,bn254AccelGlobals])
    (by rw [s1g,notAccel _ (by simp)]; exact gammaZero) (by decide) req1 fin1
  rw [bnSeqNone a1] at run
  have end1 := allocationEnd_aligned_exact (H + 416) 384 aligned416 (by decide) (by simp [BitVec.toNat_add] <;> omega)
  rw [end1] at h1
  have g1 := alloc_globals_eq s1 r1 _ _ _ (by decide) n1 h1 o1
  have chain : StoreChain bnInitGammaTail
      (.seq (.call (some ((some (.global,ofString "bn_b2")),none)) (ofString "alloc") [(.const 64)]) bnInitFieldTail) := by
    unfold bnInitGammaTail
    repeat (apply StoreChain.cons)
    exact StoreChain.nil _
  obtain ⟨m1,mg,mc,md,_,run⟩ := chain.returned run
  have aligned800 : (H + 416 + 384).toNat % 8 = 0 := (by simp [BitVec.toNat_add] <;> omega)
  obtain ⟨req2,fin2,_,_⟩ := allocation_success_bounds (H + 416 + 384) 64 (by simp [BitVec.toNat_add] <;> omega)
  obtain ⟨r2,a2,_,_,_,k2,d2,_,n2,h2,o2⟩ := evaluate_alloc_global_call m1 (.const 64) (H + 416 + 384) 64 ob2
    (ofString "bn_b2") (by simp [evalListHOLFinite,evalListHOLExact,evalHOLExact])
    (by rw [mc,k1,s1c]) (call_seq_returned_clock run) (by rw [mg,g1]; simp [*,HolFiniteMapExact.lookup_update,FUPDATE])
    (by rw [mg,g1]; simp [*,HolFiniteMapExact.lookup_update,FUPDATE]) (by decide) req2 fin2
  rw [bnSeqNone a2] at run
  have end2 := allocationEnd_aligned_exact (H + 416 + 384) 64 aligned800 (by decide) (by simp [BitVec.toNat_add] <;> omega)
  rw [end2] at h2
  have g2 := alloc_globals_eq m1 r2 _ _ _ (by decide) n2 h2 o2
  rw [mg,g1,s1g] at g2
  have installed2 : Bn254AccelInstalled r2.globals := by
    refine ⟨H,?_,?_⟩
    · rw [g2]; simp [*,HolFiniteMapExact.lookup_update,FUPDATE,bn254AccelGlobals]
    · intro e; subst e; simp at positive
  have code2 : r2.code = originalRuntimeCode := by rw [k2,mc,k1,s1c]
  unfold bnInitFieldTail at run
  obtain ⟨val,in1,run,pg1⟩ := dec_returned run
  obtain ⟨t1,in2,t1g,t1c,t1m,run,pg2⟩ := decCall_frame_step (t := setVarHOLFinite _ val r2) code2 installed2
    originalRuntimeCode_fqMul_lookup fqMul_body_frame run
  obtain ⟨t2,in3,t2g,t2c,t2m,run,pg3⟩ := decCall_frame_step t1c (by rw [t1g]; exact installed2)
    originalRuntimeCode_fqMul_lookup fqMul_body_frame run
  obtain ⟨t3,in4,t3g,t3c,t3m,run,pg4⟩ := decCall_frame_step t2c (by rw [t2g,t1g]; exact installed2)
    originalRuntimeCode_fqNeg_lookup fqNeg_body_frame run
  have t3glob : t3.globals = r2.globals := by rw [t3g,t2g,t1g]; rfl
  unfold bnInitExpTail at run
  obtain ⟨m2,m2g,m2c,_,_,run⟩ := StoreChain.returned (tail := .seq (.call (some ((some (.global,ofString "bn_expw")),none))
      (ofString "alloc") [(.panop .mul [(.const 44),(.const 8)])]) bnInitExpStores)
    (by repeat (apply StoreChain.cons)
        exact StoreChain.nil _) run
  have aligned864 : (H + 416 + 384 + 64).toNat % 8 = 0 := (by simp [BitVec.toNat_add] <;> omega)
  obtain ⟨req3,fin3,_,_⟩ := allocation_success_bounds (H + 416 + 384 + 64) 352 (by simp [BitVec.toNat_add] <;> omega)
  obtain ⟨r3,a3,_,_,_,_,_,_,n3,h3,o3⟩ := evaluate_alloc_global_call m2 (.panop .mul [.const 44,.const 8]) (H + 416 + 384 + 64) 352 oexp
    (ofString "bn_expw") (by simp [evalListHOLFinite,evalListHOLExact,evalHOLExact,panOpHOL,valueIsWord,valueWord])
    (by rw [m2c,t3c]) (call_seq_returned_clock run) (by rw [m2g,t3glob,g2]; simp [*,HolFiniteMapExact.lookup_update,FUPDATE])
    (by rw [m2g,t3glob,g2]; simp [*,HolFiniteMapExact.lookup_update,FUPDATE,bn254AccelGlobals]) (by decide) req3 fin3
  rw [bnSeqNone a3] at run
  have end3 := allocationEnd_aligned_exact (H + 416 + 384 + 64) 352 aligned864 (by decide) (by simp [BitVec.toNat_add] <;> omega)
  rw [end3] at h3
  have g3 := alloc_globals_eq m2 r3 _ _ _ (by decide) n3 h3 o3
  have chain3 : StoreChain bnInitExpStores (.return (.const 0)) := by
    unfold bnInitExpStores
    repeat (apply StoreChain.cons)
    exact StoreChain.nil _
  obtain ⟨m3,m3g,_,_,_,run⟩ := chain3.returned run
  simp [evaluateHOLFiniteState_return,evalHOLExact,shapeOfHOLExact] at run
  obtain ⟨hv,hp⟩ := run
  refine ⟨hv.symm,?_⟩
  rw [pg1,pg2,pg3,pg4,← hp]
  change m3.globals = _
  rw [m3g,g3,m2g,t3glob,g2]
  simp only [bn254InitGlobals,BitVec.add_assoc,BitVec.reduceAdd]
  rfl

#print axioms bn254Init_body_returned_cells
end InitECandidate.Runtime
