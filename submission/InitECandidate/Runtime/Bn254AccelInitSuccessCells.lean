import InitECandidate.Runtime.Bn254AccelInitSuccess
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
theorem evaluate_bn254AccelInit_body_success_cells {F : Type} (state : PanSemStateFiniteExact 64 F)
    (H : BitVec 64) (code : state.code = originalRuntimeCode)
    (heap : state.globals.lookup (ofString "heap_ptr") = some (.val (.word H)))
    (aligned : H.toNat % 8 = 0) (room : H.toNat + 2048 ≤ 33806089496)
    (zero : state.globals.lookup (ofString "bn_accel_params") = some (.val (.word 0)))
    (words : ∀ name ∈ bn254AccelNames, ∃ word : BitVec 64, state.globals.lookup name = some (.val (.word word)))
    (arena : ∀ address : BitVec 64, address.toNat % 8 = 0 → H.toNat ≤ address.toNat → address.toNat < 33806089496 → state.memaddrs address)
    (budget : 3 ≤ state.clock) :
    ∃ post : PanSemStateFiniteExact 64 F,
      evaluateHOLFiniteState state (sourceFunctionBody Guest.guestFn_bn254_accel_init) =
        (some (.returned (.val (.word 0))),post) ∧
      post.clock = state.clock - 3 ∧ post.code = state.code ∧ post.memaddrs = state.memaddrs ∧
      post.be = state.be ∧ post.globals = bn254AccelGlobals state.globals H := by
  have cell : ∀ k : Nat, k < 2048 → k % 8 = 0 → state.memaddrs (H + BitVec.ofNat 64 k) := by
    intro k hk kAligned
    have small : (BitVec.ofNat 64 k).toNat = k := by simp; omega
    have sum : (H + BitVec.ofNat 64 k).toNat = H.toNat + k := by
      rw [BitVec.toNat_add_of_lt (by omega),small]
    exact arena _ (by rw [sum]; omega) (by omega) (by omega)
  have w : ∀ name ∈ bn254AccelNames, ∃ word : BitVec 64, state.globals.lookup name = some (.val (.word word)) := words
  obtain ⟨owa,wa⟩ := w (ofString "bn_accel_a") (by simp [bn254AccelNames])
  obtain ⟨owb,wb⟩ := w (ofString "bn_accel_b") (by simp [bn254AccelNames])
  obtain ⟨owz,wz⟩ := w (ofString "bn_accel_zero") (by simp [bn254AccelNames])
  obtain ⟨owm,wm⟩ := w (ofString "bn_accel_m") (by simp [bn254AccelNames])
  obtain ⟨owd,wd⟩ := w (ofString "bn_accel_d") (by simp [bn254AccelNames])
  obtain ⟨owfp,wfp⟩ := w (ofString "bn_accel_fp2_params") (by simp [bn254AccelNames])
  obtain ⟨owf1,wf1⟩ := w (ofString "bn_accel_fp2_f1") (by simp [bn254AccelNames])
  obtain ⟨owf2,wf2⟩ := w (ofString "bn_accel_fp2_f2") (by simp [bn254AccelNames])
  obtain ⟨owg,wg⟩ := w (ofString "bn_accel_g1_params") (by simp [bn254AccelNames])
  obtain ⟨owp1,wp1⟩ := w (ofString "bn_accel_g1_p1") (by simp [bn254AccelNames])
  obtain ⟨owp2,wp2⟩ := w (ofString "bn_accel_g1_p2") (by simp [bn254AccelNames])
  have guard : evaluateHOLFiniteState state
      (.ite (.cmp .notEqual (.var .global (ofString "bn_accel_params")) (.const 0)) (.return (.const 0)) .skip) =
      (none,state) := by
    rw [evaluateHOLFiniteState_ite]
    simp [evalHOLExact,zero,Compiler.Encoders.Asm.wordCmpHOL,evaluateHOLFiniteState_skip]
  have end1 := allocationEnd_aligned_exact H 160 aligned (by decide) (by simp; omega)
  obtain ⟨r1,run1,c1,_,_,k1,d1,g1,_⟩ := evaluate_globalAllocation_prefix state
    [(ofString "bn_accel_params",160)] bnAccelTail1 H code heap (by simp; decide) (by simp; exact ⟨0,zero⟩)
    (by simpa using (allocationPlan_safe [160] H (by simp; omega)).1) (by simp; omega)
  simp only [globalAllocationGlobals] at g1
  simp only [List.length_cons,List.length_nil] at c1
  rw [end1] at g1
  have n0_1 : ofString "heap_ptr" ≠ ofString "bn_accel_params" := by decide
  have n1_0 : ofString "bn_accel_params" ≠ ofString "heap_ptr" := by decide
  have n0_2 : ofString "heap_ptr" ≠ ofString "bn_accel_a" := by decide
  have n2_0 : ofString "bn_accel_a" ≠ ofString "heap_ptr" := by decide
  have n0_3 : ofString "heap_ptr" ≠ ofString "bn_accel_b" := by decide
  have n3_0 : ofString "bn_accel_b" ≠ ofString "heap_ptr" := by decide
  have n0_4 : ofString "heap_ptr" ≠ ofString "bn_accel_zero" := by decide
  have n4_0 : ofString "bn_accel_zero" ≠ ofString "heap_ptr" := by decide
  have n0_5 : ofString "heap_ptr" ≠ ofString "bn_accel_m" := by decide
  have n5_0 : ofString "bn_accel_m" ≠ ofString "heap_ptr" := by decide
  have n0_6 : ofString "heap_ptr" ≠ ofString "bn_accel_d" := by decide
  have n6_0 : ofString "bn_accel_d" ≠ ofString "heap_ptr" := by decide
  have n0_7 : ofString "heap_ptr" ≠ ofString "bn_accel_fp2_params" := by decide
  have n7_0 : ofString "bn_accel_fp2_params" ≠ ofString "heap_ptr" := by decide
  have n0_8 : ofString "heap_ptr" ≠ ofString "bn_accel_fp2_f1" := by decide
  have n8_0 : ofString "bn_accel_fp2_f1" ≠ ofString "heap_ptr" := by decide
  have n0_9 : ofString "heap_ptr" ≠ ofString "bn_accel_fp2_f2" := by decide
  have n9_0 : ofString "bn_accel_fp2_f2" ≠ ofString "heap_ptr" := by decide
  have n0_10 : ofString "heap_ptr" ≠ ofString "bn_accel_g1_params" := by decide
  have n10_0 : ofString "bn_accel_g1_params" ≠ ofString "heap_ptr" := by decide
  have n0_11 : ofString "heap_ptr" ≠ ofString "bn_accel_g1_p1" := by decide
  have n11_0 : ofString "bn_accel_g1_p1" ≠ ofString "heap_ptr" := by decide
  have n0_12 : ofString "heap_ptr" ≠ ofString "bn_accel_g1_p2" := by decide
  have n12_0 : ofString "bn_accel_g1_p2" ≠ ofString "heap_ptr" := by decide
  have n1_2 : ofString "bn_accel_params" ≠ ofString "bn_accel_a" := by decide
  have n2_1 : ofString "bn_accel_a" ≠ ofString "bn_accel_params" := by decide
  have n1_3 : ofString "bn_accel_params" ≠ ofString "bn_accel_b" := by decide
  have n3_1 : ofString "bn_accel_b" ≠ ofString "bn_accel_params" := by decide
  have n1_4 : ofString "bn_accel_params" ≠ ofString "bn_accel_zero" := by decide
  have n4_1 : ofString "bn_accel_zero" ≠ ofString "bn_accel_params" := by decide
  have n1_5 : ofString "bn_accel_params" ≠ ofString "bn_accel_m" := by decide
  have n5_1 : ofString "bn_accel_m" ≠ ofString "bn_accel_params" := by decide
  have n1_6 : ofString "bn_accel_params" ≠ ofString "bn_accel_d" := by decide
  have n6_1 : ofString "bn_accel_d" ≠ ofString "bn_accel_params" := by decide
  have n1_7 : ofString "bn_accel_params" ≠ ofString "bn_accel_fp2_params" := by decide
  have n7_1 : ofString "bn_accel_fp2_params" ≠ ofString "bn_accel_params" := by decide
  have n1_8 : ofString "bn_accel_params" ≠ ofString "bn_accel_fp2_f1" := by decide
  have n8_1 : ofString "bn_accel_fp2_f1" ≠ ofString "bn_accel_params" := by decide
  have n1_9 : ofString "bn_accel_params" ≠ ofString "bn_accel_fp2_f2" := by decide
  have n9_1 : ofString "bn_accel_fp2_f2" ≠ ofString "bn_accel_params" := by decide
  have n1_10 : ofString "bn_accel_params" ≠ ofString "bn_accel_g1_params" := by decide
  have n10_1 : ofString "bn_accel_g1_params" ≠ ofString "bn_accel_params" := by decide
  have n1_11 : ofString "bn_accel_params" ≠ ofString "bn_accel_g1_p1" := by decide
  have n11_1 : ofString "bn_accel_g1_p1" ≠ ofString "bn_accel_params" := by decide
  have n1_12 : ofString "bn_accel_params" ≠ ofString "bn_accel_g1_p2" := by decide
  have n12_1 : ofString "bn_accel_g1_p2" ≠ ofString "bn_accel_params" := by decide
  have n2_3 : ofString "bn_accel_a" ≠ ofString "bn_accel_b" := by decide
  have n3_2 : ofString "bn_accel_b" ≠ ofString "bn_accel_a" := by decide
  have n2_4 : ofString "bn_accel_a" ≠ ofString "bn_accel_zero" := by decide
  have n4_2 : ofString "bn_accel_zero" ≠ ofString "bn_accel_a" := by decide
  have n2_5 : ofString "bn_accel_a" ≠ ofString "bn_accel_m" := by decide
  have n5_2 : ofString "bn_accel_m" ≠ ofString "bn_accel_a" := by decide
  have n2_6 : ofString "bn_accel_a" ≠ ofString "bn_accel_d" := by decide
  have n6_2 : ofString "bn_accel_d" ≠ ofString "bn_accel_a" := by decide
  have n2_7 : ofString "bn_accel_a" ≠ ofString "bn_accel_fp2_params" := by decide
  have n7_2 : ofString "bn_accel_fp2_params" ≠ ofString "bn_accel_a" := by decide
  have n2_8 : ofString "bn_accel_a" ≠ ofString "bn_accel_fp2_f1" := by decide
  have n8_2 : ofString "bn_accel_fp2_f1" ≠ ofString "bn_accel_a" := by decide
  have n2_9 : ofString "bn_accel_a" ≠ ofString "bn_accel_fp2_f2" := by decide
  have n9_2 : ofString "bn_accel_fp2_f2" ≠ ofString "bn_accel_a" := by decide
  have n2_10 : ofString "bn_accel_a" ≠ ofString "bn_accel_g1_params" := by decide
  have n10_2 : ofString "bn_accel_g1_params" ≠ ofString "bn_accel_a" := by decide
  have n2_11 : ofString "bn_accel_a" ≠ ofString "bn_accel_g1_p1" := by decide
  have n11_2 : ofString "bn_accel_g1_p1" ≠ ofString "bn_accel_a" := by decide
  have n2_12 : ofString "bn_accel_a" ≠ ofString "bn_accel_g1_p2" := by decide
  have n12_2 : ofString "bn_accel_g1_p2" ≠ ofString "bn_accel_a" := by decide
  have n3_4 : ofString "bn_accel_b" ≠ ofString "bn_accel_zero" := by decide
  have n4_3 : ofString "bn_accel_zero" ≠ ofString "bn_accel_b" := by decide
  have n3_5 : ofString "bn_accel_b" ≠ ofString "bn_accel_m" := by decide
  have n5_3 : ofString "bn_accel_m" ≠ ofString "bn_accel_b" := by decide
  have n3_6 : ofString "bn_accel_b" ≠ ofString "bn_accel_d" := by decide
  have n6_3 : ofString "bn_accel_d" ≠ ofString "bn_accel_b" := by decide
  have n3_7 : ofString "bn_accel_b" ≠ ofString "bn_accel_fp2_params" := by decide
  have n7_3 : ofString "bn_accel_fp2_params" ≠ ofString "bn_accel_b" := by decide
  have n3_8 : ofString "bn_accel_b" ≠ ofString "bn_accel_fp2_f1" := by decide
  have n8_3 : ofString "bn_accel_fp2_f1" ≠ ofString "bn_accel_b" := by decide
  have n3_9 : ofString "bn_accel_b" ≠ ofString "bn_accel_fp2_f2" := by decide
  have n9_3 : ofString "bn_accel_fp2_f2" ≠ ofString "bn_accel_b" := by decide
  have n3_10 : ofString "bn_accel_b" ≠ ofString "bn_accel_g1_params" := by decide
  have n10_3 : ofString "bn_accel_g1_params" ≠ ofString "bn_accel_b" := by decide
  have n3_11 : ofString "bn_accel_b" ≠ ofString "bn_accel_g1_p1" := by decide
  have n11_3 : ofString "bn_accel_g1_p1" ≠ ofString "bn_accel_b" := by decide
  have n3_12 : ofString "bn_accel_b" ≠ ofString "bn_accel_g1_p2" := by decide
  have n12_3 : ofString "bn_accel_g1_p2" ≠ ofString "bn_accel_b" := by decide
  have n4_5 : ofString "bn_accel_zero" ≠ ofString "bn_accel_m" := by decide
  have n5_4 : ofString "bn_accel_m" ≠ ofString "bn_accel_zero" := by decide
  have n4_6 : ofString "bn_accel_zero" ≠ ofString "bn_accel_d" := by decide
  have n6_4 : ofString "bn_accel_d" ≠ ofString "bn_accel_zero" := by decide
  have n4_7 : ofString "bn_accel_zero" ≠ ofString "bn_accel_fp2_params" := by decide
  have n7_4 : ofString "bn_accel_fp2_params" ≠ ofString "bn_accel_zero" := by decide
  have n4_8 : ofString "bn_accel_zero" ≠ ofString "bn_accel_fp2_f1" := by decide
  have n8_4 : ofString "bn_accel_fp2_f1" ≠ ofString "bn_accel_zero" := by decide
  have n4_9 : ofString "bn_accel_zero" ≠ ofString "bn_accel_fp2_f2" := by decide
  have n9_4 : ofString "bn_accel_fp2_f2" ≠ ofString "bn_accel_zero" := by decide
  have n4_10 : ofString "bn_accel_zero" ≠ ofString "bn_accel_g1_params" := by decide
  have n10_4 : ofString "bn_accel_g1_params" ≠ ofString "bn_accel_zero" := by decide
  have n4_11 : ofString "bn_accel_zero" ≠ ofString "bn_accel_g1_p1" := by decide
  have n11_4 : ofString "bn_accel_g1_p1" ≠ ofString "bn_accel_zero" := by decide
  have n4_12 : ofString "bn_accel_zero" ≠ ofString "bn_accel_g1_p2" := by decide
  have n12_4 : ofString "bn_accel_g1_p2" ≠ ofString "bn_accel_zero" := by decide
  have n5_6 : ofString "bn_accel_m" ≠ ofString "bn_accel_d" := by decide
  have n6_5 : ofString "bn_accel_d" ≠ ofString "bn_accel_m" := by decide
  have n5_7 : ofString "bn_accel_m" ≠ ofString "bn_accel_fp2_params" := by decide
  have n7_5 : ofString "bn_accel_fp2_params" ≠ ofString "bn_accel_m" := by decide
  have n5_8 : ofString "bn_accel_m" ≠ ofString "bn_accel_fp2_f1" := by decide
  have n8_5 : ofString "bn_accel_fp2_f1" ≠ ofString "bn_accel_m" := by decide
  have n5_9 : ofString "bn_accel_m" ≠ ofString "bn_accel_fp2_f2" := by decide
  have n9_5 : ofString "bn_accel_fp2_f2" ≠ ofString "bn_accel_m" := by decide
  have n5_10 : ofString "bn_accel_m" ≠ ofString "bn_accel_g1_params" := by decide
  have n10_5 : ofString "bn_accel_g1_params" ≠ ofString "bn_accel_m" := by decide
  have n5_11 : ofString "bn_accel_m" ≠ ofString "bn_accel_g1_p1" := by decide
  have n11_5 : ofString "bn_accel_g1_p1" ≠ ofString "bn_accel_m" := by decide
  have n5_12 : ofString "bn_accel_m" ≠ ofString "bn_accel_g1_p2" := by decide
  have n12_5 : ofString "bn_accel_g1_p2" ≠ ofString "bn_accel_m" := by decide
  have n6_7 : ofString "bn_accel_d" ≠ ofString "bn_accel_fp2_params" := by decide
  have n7_6 : ofString "bn_accel_fp2_params" ≠ ofString "bn_accel_d" := by decide
  have n6_8 : ofString "bn_accel_d" ≠ ofString "bn_accel_fp2_f1" := by decide
  have n8_6 : ofString "bn_accel_fp2_f1" ≠ ofString "bn_accel_d" := by decide
  have n6_9 : ofString "bn_accel_d" ≠ ofString "bn_accel_fp2_f2" := by decide
  have n9_6 : ofString "bn_accel_fp2_f2" ≠ ofString "bn_accel_d" := by decide
  have n6_10 : ofString "bn_accel_d" ≠ ofString "bn_accel_g1_params" := by decide
  have n10_6 : ofString "bn_accel_g1_params" ≠ ofString "bn_accel_d" := by decide
  have n6_11 : ofString "bn_accel_d" ≠ ofString "bn_accel_g1_p1" := by decide
  have n11_6 : ofString "bn_accel_g1_p1" ≠ ofString "bn_accel_d" := by decide
  have n6_12 : ofString "bn_accel_d" ≠ ofString "bn_accel_g1_p2" := by decide
  have n12_6 : ofString "bn_accel_g1_p2" ≠ ofString "bn_accel_d" := by decide
  have n7_8 : ofString "bn_accel_fp2_params" ≠ ofString "bn_accel_fp2_f1" := by decide
  have n8_7 : ofString "bn_accel_fp2_f1" ≠ ofString "bn_accel_fp2_params" := by decide
  have n7_9 : ofString "bn_accel_fp2_params" ≠ ofString "bn_accel_fp2_f2" := by decide
  have n9_7 : ofString "bn_accel_fp2_f2" ≠ ofString "bn_accel_fp2_params" := by decide
  have n7_10 : ofString "bn_accel_fp2_params" ≠ ofString "bn_accel_g1_params" := by decide
  have n10_7 : ofString "bn_accel_g1_params" ≠ ofString "bn_accel_fp2_params" := by decide
  have n7_11 : ofString "bn_accel_fp2_params" ≠ ofString "bn_accel_g1_p1" := by decide
  have n11_7 : ofString "bn_accel_g1_p1" ≠ ofString "bn_accel_fp2_params" := by decide
  have n7_12 : ofString "bn_accel_fp2_params" ≠ ofString "bn_accel_g1_p2" := by decide
  have n12_7 : ofString "bn_accel_g1_p2" ≠ ofString "bn_accel_fp2_params" := by decide
  have n8_9 : ofString "bn_accel_fp2_f1" ≠ ofString "bn_accel_fp2_f2" := by decide
  have n9_8 : ofString "bn_accel_fp2_f2" ≠ ofString "bn_accel_fp2_f1" := by decide
  have n8_10 : ofString "bn_accel_fp2_f1" ≠ ofString "bn_accel_g1_params" := by decide
  have n10_8 : ofString "bn_accel_g1_params" ≠ ofString "bn_accel_fp2_f1" := by decide
  have n8_11 : ofString "bn_accel_fp2_f1" ≠ ofString "bn_accel_g1_p1" := by decide
  have n11_8 : ofString "bn_accel_g1_p1" ≠ ofString "bn_accel_fp2_f1" := by decide
  have n8_12 : ofString "bn_accel_fp2_f1" ≠ ofString "bn_accel_g1_p2" := by decide
  have n12_8 : ofString "bn_accel_g1_p2" ≠ ofString "bn_accel_fp2_f1" := by decide
  have n9_10 : ofString "bn_accel_fp2_f2" ≠ ofString "bn_accel_g1_params" := by decide
  have n10_9 : ofString "bn_accel_g1_params" ≠ ofString "bn_accel_fp2_f2" := by decide
  have n9_11 : ofString "bn_accel_fp2_f2" ≠ ofString "bn_accel_g1_p1" := by decide
  have n11_9 : ofString "bn_accel_g1_p1" ≠ ofString "bn_accel_fp2_f2" := by decide
  have n9_12 : ofString "bn_accel_fp2_f2" ≠ ofString "bn_accel_g1_p2" := by decide
  have n12_9 : ofString "bn_accel_g1_p2" ≠ ofString "bn_accel_fp2_f2" := by decide
  have n10_11 : ofString "bn_accel_g1_params" ≠ ofString "bn_accel_g1_p1" := by decide
  have n11_10 : ofString "bn_accel_g1_p1" ≠ ofString "bn_accel_g1_params" := by decide
  have n10_12 : ofString "bn_accel_g1_params" ≠ ofString "bn_accel_g1_p2" := by decide
  have n12_10 : ofString "bn_accel_g1_p2" ≠ ofString "bn_accel_g1_params" := by decide
  have n11_12 : ofString "bn_accel_g1_p1" ≠ ofString "bn_accel_g1_p2" := by decide
  have n12_11 : ofString "bn_accel_g1_p2" ≠ ofString "bn_accel_g1_p1" := by decide
  have h1 : r1.globals.lookup (ofString "heap_ptr") = some (.val (.word (H + 160))) := by
    rw [g1]; simp [*,HolFiniteMapExact.lookup_update,FUPDATE]
  have dom : ∀ {G : Type} (t : PanSemStateFiniteExact 64 G), t.memaddrs = state.memaddrs → True := fun _ _ => trivial
  let s1 := setGlobalHOLFinite (ofString "bn_accel_a") (.val (.word (H))) r1
  have e1 : evaluateHOLFiniteState r1 (.assign .global (ofString "bn_accel_a") (.var .global (ofString "bn_accel_params"))) = (none,s1) :=
    evaluate_assign_global_word r1 _ _ owa (H) (by simp [*,g1,HolFiniteMapExact.lookup_update,FUPDATE,setGlobalHOLFinite,journalRecordPost32,sourceWriteWord]) (by simp [*,evalHOLExact,evalListHOLExact,wordOpHOL,wordOp,valueIsWord,valueWord,g1,HolFiniteMapExact.lookup_update,FUPDATE,setGlobalHOLFinite,journalRecordPost32,sourceWriteWord])
  let s2 := setGlobalHOLFinite (ofString "bn_accel_b") (.val (.word (H + 32))) s1
  have e2 : evaluateHOLFiniteState s1 (.assign .global (ofString "bn_accel_b") (.op .add [.var .global (ofString "bn_accel_params"),.const 32])) = (none,s2) :=
    evaluate_assign_global_word s1 _ _ owb (H + 32) (by simp [*,s1,g1,HolFiniteMapExact.lookup_update,FUPDATE,setGlobalHOLFinite,journalRecordPost32,sourceWriteWord]) (by simp [*,s1,evalHOLExact,evalListHOLExact,wordOpHOL,wordOp,valueIsWord,valueWord,g1,HolFiniteMapExact.lookup_update,FUPDATE,setGlobalHOLFinite,journalRecordPost32,sourceWriteWord])
  let s3 := setGlobalHOLFinite (ofString "bn_accel_zero") (.val (.word (H + 64))) s2
  have e3 : evaluateHOLFiniteState s2 (.assign .global (ofString "bn_accel_zero") (.op .add [.var .global (ofString "bn_accel_params"),.const 64])) = (none,s3) :=
    evaluate_assign_global_word s2 _ _ owz (H + 64) (by simp [*,s1,s2,g1,HolFiniteMapExact.lookup_update,FUPDATE,setGlobalHOLFinite,journalRecordPost32,sourceWriteWord]) (by simp [*,s1,s2,evalHOLExact,evalListHOLExact,wordOpHOL,wordOp,valueIsWord,valueWord,g1,HolFiniteMapExact.lookup_update,FUPDATE,setGlobalHOLFinite,journalRecordPost32,sourceWriteWord])
  let s4 := setGlobalHOLFinite (ofString "bn_accel_m") (.val (.word (H + 96))) s3
  have e4 : evaluateHOLFiniteState s3 (.assign .global (ofString "bn_accel_m") (.op .add [.var .global (ofString "bn_accel_params"),.const 96])) = (none,s4) :=
    evaluate_assign_global_word s3 _ _ owm (H + 96) (by simp [*,s1,s2,s3,g1,HolFiniteMapExact.lookup_update,FUPDATE,setGlobalHOLFinite,journalRecordPost32,sourceWriteWord]) (by simp [*,s1,s2,s3,evalHOLExact,evalListHOLExact,wordOpHOL,wordOp,valueIsWord,valueWord,g1,HolFiniteMapExact.lookup_update,FUPDATE,setGlobalHOLFinite,journalRecordPost32,sourceWriteWord])
  let s5 := setGlobalHOLFinite (ofString "bn_accel_d") (.val (.word (H + 128))) s4
  have e5 : evaluateHOLFiniteState s4 (.assign .global (ofString "bn_accel_d") (.op .add [.var .global (ofString "bn_accel_params"),.const 128])) = (none,s5) :=
    evaluate_assign_global_word s4 _ _ owd (H + 128) (by simp [*,s1,s2,s3,s4,g1,HolFiniteMapExact.lookup_update,FUPDATE,setGlobalHOLFinite,journalRecordPost32,sourceWriteWord]) (by simp [*,s1,s2,s3,s4,evalHOLExact,evalListHOLExact,wordOpHOL,wordOp,valueIsWord,valueWord,g1,HolFiniteMapExact.lookup_update,FUPDATE,setGlobalHOLFinite,journalRecordPost32,sourceWriteWord])
  let s6 := journalRecordPost32 s5 (H + 64) (0) (0) (0) (0)
  have e6 : evaluateHOLFiniteState s5 (.store (.var .global (ofString "bn_accel_zero")) (.rstruct [.const 0,.const 0,.const 0,.const 0])) = (none,s6) :=
    evaluate_store_four_words s5 (H + 64) (0) (0) (0) (0) _ _ (by simp [*,s1,s2,s3,s4,s5,evalHOLExact,evalListHOLExact,wordOpHOL,wordOp,valueIsWord,valueWord,g1,HolFiniteMapExact.lookup_update,FUPDATE,setGlobalHOLFinite,journalRecordPost32,sourceWriteWord]) (by simp [evalHOLExact,evalListHOLExact,wordOpHOL,wordOp,valueIsWord,valueWord])
      (by change r1.memaddrs (H + 64); rw [d1]; exact cell 64 (by omega) (by decide)) (by change r1.memaddrs ((H + 64) + 8); rw [d1,BitVec.add_assoc]; exact cell 72 (by omega) (by decide))
      (by change r1.memaddrs ((H + 64) + 16); rw [d1,BitVec.add_assoc]; exact cell 80 (by omega) (by decide)) (by change r1.memaddrs ((H + 64) + 24); rw [d1,BitVec.add_assoc]; exact cell 88 (by omega) (by decide))
  let s7 := journalRecordPost32 s6 (H + 96) (4332616871279656263) (10917124144477883021) (13281191951274694749) (3486998266802970665)
  have e7 : evaluateHOLFiniteState s6 (.store (.var .global (ofString "bn_accel_m")) (.rstruct [.const 4332616871279656263,.const 10917124144477883021,.const 13281191951274694749,.const 3486998266802970665])) = (none,s7) :=
    evaluate_store_four_words s6 (H + 96) (4332616871279656263) (10917124144477883021) (13281191951274694749) (3486998266802970665) _ _ (by simp [*,s1,s2,s3,s4,s5,s6,evalHOLExact,evalListHOLExact,wordOpHOL,wordOp,valueIsWord,valueWord,g1,HolFiniteMapExact.lookup_update,FUPDATE,setGlobalHOLFinite,journalRecordPost32,sourceWriteWord]) (by simp [evalHOLExact,evalListHOLExact,wordOpHOL,wordOp,valueIsWord,valueWord])
      (by change r1.memaddrs (H + 96); rw [d1]; exact cell 96 (by omega) (by decide)) (by change r1.memaddrs ((H + 96) + 8); rw [d1,BitVec.add_assoc]; exact cell 104 (by omega) (by decide))
      (by change r1.memaddrs ((H + 96) + 16); rw [d1,BitVec.add_assoc]; exact cell 112 (by omega) (by decide)) (by change r1.memaddrs ((H + 96) + 24); rw [d1,BitVec.add_assoc]; exact cell 120 (by omega) (by decide))
  have tail1 : evaluateHOLFiniteState r1 bnAccelTail1 =
      evaluateHOLFiniteState s7 (globalAllocationProgram [(ofString "bn_accel_fp2_params",128)] bnAccelTail2) := by
    unfold bnAccelTail1
    rw [bnSeqNone e1,bnSeqNone e2,bnSeqNone e3,bnSeqNone e4,bnSeqNone e5,bnSeqNone e6,bnSeqNone e7]
  have end2 := allocationEnd_aligned_exact (H + 160) 128 (by rw [BitVec.toNat_add_of_lt (by simp; omega)]; simp; omega) (by decide)
    (by rw [BitVec.toNat_add_of_lt (by simp; omega)]; simp; omega)
  have heap7 : s7.globals.lookup (ofString "heap_ptr") = some (.val (.word (H + 160))) := by
    simp [*,s1,s2,s3,s4,s5,s6,s7,g1,HolFiniteMapExact.lookup_update,FUPDATE,setGlobalHOLFinite,journalRecordPost32,sourceWriteWord]
  obtain ⟨r2,run2,c2,_,_,k2,d2,g2,_⟩ := evaluate_globalAllocation_prefix s7
    [(ofString "bn_accel_fp2_params",128)] bnAccelTail2 (H + 160) (by change r1.code = _; rw [k1,code]) heap7 (by simp; decide)
    (by simp; exact ⟨owfp,by simp [*,s1,s2,s3,s4,s5,s6,s7,g1,HolFiniteMapExact.lookup_update,FUPDATE,setGlobalHOLFinite,journalRecordPost32,sourceWriteWord]⟩)
    (by simpa using (allocationPlan_safe [128] (H + 160) (by rw [BitVec.toNat_add_of_lt (by simp; omega)]; simp; omega)).1)
    (by simp; change 1 ≤ r1.clock; omega)
  simp only [globalAllocationGlobals] at g2
  simp only [List.length_cons,List.length_nil] at c2
  rw [end2,BitVec.add_assoc] at g2
  let s8 := setGlobalHOLFinite (ofString "bn_accel_fp2_f1") (.val (.word (H + 160))) r2
  have e8 : evaluateHOLFiniteState r2 (.assign .global (ofString "bn_accel_fp2_f1") (.var .global (ofString "bn_accel_fp2_params"))) = (none,s8) :=
    evaluate_assign_global_word r2 _ _ owf1 (H + 160) (by simp [*,g2,g1,s1,s2,s3,s4,s5,s6,s7,HolFiniteMapExact.lookup_update,FUPDATE,setGlobalHOLFinite,journalRecordPost32,sourceWriteWord]) (by simp [*,evalHOLExact,evalListHOLExact,wordOpHOL,wordOp,valueIsWord,valueWord,g2,g1,s1,s2,s3,s4,s5,s6,s7,HolFiniteMapExact.lookup_update,FUPDATE,setGlobalHOLFinite,journalRecordPost32,sourceWriteWord])
  let s9 := setGlobalHOLFinite (ofString "bn_accel_fp2_f2") (.val (.word (H + 160 + 64))) s8
  have e9 : evaluateHOLFiniteState s8 (.assign .global (ofString "bn_accel_fp2_f2") (.op .add [.var .global (ofString "bn_accel_fp2_params"),.const 64])) = (none,s9) :=
    evaluate_assign_global_word s8 _ _ owf2 (H + 160 + 64) (by simp [*,s8,g2,g1,s1,s2,s3,s4,s5,s6,s7,HolFiniteMapExact.lookup_update,FUPDATE,setGlobalHOLFinite,journalRecordPost32,sourceWriteWord]) (by simp [*,s8,evalHOLExact,evalListHOLExact,wordOpHOL,wordOp,valueIsWord,valueWord,g2,g1,s1,s2,s3,s4,s5,s6,s7,HolFiniteMapExact.lookup_update,FUPDATE,setGlobalHOLFinite,journalRecordPost32,sourceWriteWord])
  have tail2 : evaluateHOLFiniteState r2 bnAccelTail2 =
      evaluateHOLFiniteState s9 (globalAllocationProgram [(ofString "bn_accel_g1_params",128)] bnAccelTail3) := by
    unfold bnAccelTail2
    rw [bnSeqNone e8,bnSeqNone e9]
  have end3 := allocationEnd_aligned_exact (H + (160 + 128)) 128 (by rw [BitVec.toNat_add_of_lt (by simp; omega)]; simp; omega) (by decide)
    (by rw [BitVec.toNat_add_of_lt (by simp; omega)]; simp; omega)
  have heap9 : s9.globals.lookup (ofString "heap_ptr") = some (.val (.word (H + (160 + 128)))) := by
    simp [*,s9,s8,g2,HolFiniteMapExact.lookup_update,FUPDATE,setGlobalHOLFinite,journalRecordPost32,sourceWriteWord]
  obtain ⟨r3,run3,c3,_,_,k3,d3,g3,_⟩ := evaluate_globalAllocation_prefix s9
    [(ofString "bn_accel_g1_params",128)] bnAccelTail3 (H + (160 + 128)) (by change r2.code = _; rw [k2]; change r1.code = _; rw [k1,code]) heap9 (by simp; decide)
    (by simp; exact ⟨owg,by simp [*,s9,s8,g2,g1,s1,s2,s3,s4,s5,s6,s7,HolFiniteMapExact.lookup_update,FUPDATE,setGlobalHOLFinite,journalRecordPost32,sourceWriteWord]⟩)
    (by simpa using (allocationPlan_safe [128] (H + (160 + 128)) (by rw [BitVec.toNat_add_of_lt (by simp; omega)]; simp; omega)).1)
    (by show 1 ≤ r2.clock; change r2.clock = r1.clock - 1 at c2; omega)
  simp only [globalAllocationGlobals] at g3
  simp only [List.length_cons,List.length_nil] at c3
  rw [end3,BitVec.add_assoc] at g3
  let s10 := setGlobalHOLFinite (ofString "bn_accel_g1_p1") (.val (.word (H + (160 + 128)))) r3
  have e10 : evaluateHOLFiniteState r3 (.assign .global (ofString "bn_accel_g1_p1") (.var .global (ofString "bn_accel_g1_params"))) = (none,s10) :=
    evaluate_assign_global_word r3 _ _ owp1 (H + (160 + 128)) (by simp [*,s9,s8,g2,g1,s1,s2,s3,s4,s5,s6,s7,g3,HolFiniteMapExact.lookup_update,FUPDATE,setGlobalHOLFinite,journalRecordPost32,sourceWriteWord]) (by simp [*,s9,s8,g2,g1,s1,s2,s3,s4,s5,s6,s7,evalHOLExact,evalListHOLExact,wordOpHOL,wordOp,valueIsWord,valueWord,g3,HolFiniteMapExact.lookup_update,FUPDATE,setGlobalHOLFinite,journalRecordPost32,sourceWriteWord])
  let s11 := setGlobalHOLFinite (ofString "bn_accel_g1_p2") (.val (.word (H + (160 + 128) + 64))) s10
  have e11 : evaluateHOLFiniteState s10 (.assign .global (ofString "bn_accel_g1_p2") (.op .add [.var .global (ofString "bn_accel_g1_params"),.const 64])) = (none,s11) :=
    evaluate_assign_global_word s10 _ _ owp2 (H + (160 + 128) + 64) (by simp [*,s9,s8,g2,g1,s1,s2,s3,s4,s5,s6,s7,s10,g3,HolFiniteMapExact.lookup_update,FUPDATE,setGlobalHOLFinite,journalRecordPost32,sourceWriteWord]) (by simp [*,s9,s8,g2,g1,s1,s2,s3,s4,s5,s6,s7,s10,evalHOLExact,evalListHOLExact,wordOpHOL,wordOp,valueIsWord,valueWord,g3,HolFiniteMapExact.lookup_update,FUPDATE,setGlobalHOLFinite,journalRecordPost32,sourceWriteWord])
  have tail3 : evaluateHOLFiniteState r3 bnAccelTail3 = evaluateHOLFiniteState s11 (.return (.const 0)) := by
    unfold bnAccelTail3
    rw [bnSeqNone e10,bnSeqNone e11]
  have run : evaluateHOLFiniteState state (sourceFunctionBody Guest.guestFn_bn254_accel_init) =
      (some (.returned (.val (.word 0))),emptyLocalsHOLFinite s11) := by
    rw [source_bn254AccelInit_body,bnSeqNone guard,run1,tail1,run2,tail2,run3,tail3]
    simp [evaluateHOLFiniteState_return,evalHOLExact,shapeOfHOLExact,sizeOfShapeWithContextHOL]
  refine ⟨_,run,?_,?_,?_,?_,?_⟩
  · change r3.clock = state.clock - 3
    change r3.clock = r2.clock - 1 at c3
    change r2.clock = r1.clock - 1 at c2
    omega
  · change r3.code = state.code
    rw [k3]; change r2.code = _; rw [k2]; change r1.code = _; rw [k1]
  · change r3.memaddrs = state.memaddrs
    rw [d3]; change r2.memaddrs = _; rw [d2]; change r1.memaddrs = _; rw [d1]
  · have m := evaluateHOLFiniteState_metadata state (sourceFunctionBody Guest.guestFn_bn254_accel_init)
    rw [run] at m
    exact m.2.2.1
  · change s11.globals = _
    simp only [s11,s10,setGlobalHOLFinite]
    rw [g3]
    simp only [s9,s8,setGlobalHOLFinite]
    rw [g2]
    simp only [s7,s6,s5,s4,s3,s2,s1,journalRecordPost32,sourceWriteWord,setGlobalHOLFinite]
    rw [g1]
    simp only [bn254AccelGlobals,BitVec.add_assoc,BitVec.reduceAdd]
    rfl

#print axioms evaluate_bn254AccelInit_body_success_cells
end InitECandidate.Runtime
