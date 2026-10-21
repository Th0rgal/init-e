import InitECandidate.Runtime.GuestWordCostSupportFirst
import InitECandidate.Runtime.GuestWordFrameCoverage
import InitECandidate.Proofs.BackendStages.Native
namespace InitECandidate.Runtime.WordToStack
open Flapjack InitECandidate.Proofs.BackendStages
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 100000000

/-- Boolean eligibility of the concrete allocated Word declaration table. -/
def wordCodeCostSupported (programs : List (Nat × Nat × WordLangProgHOL (BitVec 64))) : Bool :=
  programs.all (fun entry => wordCostSupported entry.2.2)

theorem wordCodeCostSupported_append (a b : List (Nat × Nat × WordLangProgHOL (BitVec 64))) :
    wordCodeCostSupported (a++b) = (wordCodeCostSupported a && wordCodeCostSupported b) := by
  simp [wordCodeCostSupported]

theorem costSupported_Chunk80_95 : wordCodeCostSupported Chunk80_95.programs = true := by
  decide_cbv
theorem costSupported_Chunk96_111 : wordCodeCostSupported Chunk96_111.programs = true := by
  decide_cbv
theorem costSupported_Chunk112_127 : wordCodeCostSupported Chunk112_127.programs = true := by
  decide_cbv
theorem costSupported_Chunk128_143 : wordCodeCostSupported Chunk128_143.programs = true := by
  decide_cbv
theorem costSupported_Chunk144_159 : wordCodeCostSupported Chunk144_159.programs = true := by
  decide_cbv
theorem costSupported_Chunk160_175 : wordCodeCostSupported Chunk160_175.programs = true := by
  decide_cbv
theorem costSupported_Chunk176_191 : wordCodeCostSupported Chunk176_191.programs = true := by
  decide_cbv
theorem costSupported_Chunk192_207 : wordCodeCostSupported Chunk192_207.programs = true := by
  decide_cbv
theorem costSupported_Chunk208_223 : wordCodeCostSupported Chunk208_223.programs = true := by
  decide_cbv
theorem costSupported_Chunk224_239 : wordCodeCostSupported Chunk224_239.programs = true := by
  decide_cbv
theorem costSupported_Chunk240_255 : wordCodeCostSupported Chunk240_255.programs = true := by
  decide_cbv
theorem costSupported_Chunk256_271 : wordCodeCostSupported Chunk256_271.programs = true := by
  decide_cbv
theorem costSupported_Chunk272_287 : wordCodeCostSupported Chunk272_287.programs = true := by
  decide_cbv
theorem costSupported_Chunk288_303 : wordCodeCostSupported Chunk288_303.programs = true := by
  decide_cbv
theorem costSupported_Chunk304_319 : wordCodeCostSupported Chunk304_319.programs = true := by
  decide_cbv
theorem costSupported_Chunk320_335 : wordCodeCostSupported Chunk320_335.programs = true := by
  decide_cbv
theorem costSupported_Chunk336_351 : wordCodeCostSupported Chunk336_351.programs = true := by
  decide_cbv
theorem costSupported_Chunk352_367 : wordCodeCostSupported Chunk352_367.programs = true := by
  decide_cbv
theorem costSupported_Chunk368_383 : wordCodeCostSupported Chunk368_383.programs = true := by
  decide_cbv
theorem costSupported_Chunk384_399 : wordCodeCostSupported Chunk384_399.programs = true := by
  decide_cbv
theorem costSupported_Chunk400_415 : wordCodeCostSupported Chunk400_415.programs = true := by
  decide_cbv
theorem costSupported_Chunk416_431 : wordCodeCostSupported Chunk416_431.programs = true := by
  decide_cbv
theorem costSupported_Chunk432_447 : wordCodeCostSupported Chunk432_447.programs = true := by
  decide_cbv
theorem costSupported_Chunk448_463 : wordCodeCostSupported Chunk448_463.programs = true := by
  decide_cbv
theorem costSupported_Chunk464_479 : wordCodeCostSupported Chunk464_479.programs = true := by
  decide_cbv
theorem costSupported_Chunk480_495 : wordCodeCostSupported Chunk480_495.programs = true := by
  decide_cbv
theorem costSupported_Chunk496_511 : wordCodeCostSupported Chunk496_511.programs = true := by
  decide_cbv
theorem costSupported_Chunk512_527 : wordCodeCostSupported Chunk512_527.programs = true := by
  decide_cbv
theorem costSupported_Chunk528_543 : wordCodeCostSupported Chunk528_543.programs = true := by
  decide_cbv
theorem costSupported_Chunk544_559 : wordCodeCostSupported Chunk544_559.programs = true := by
  decide_cbv
theorem costSupported_Chunk560_575 : wordCodeCostSupported Chunk560_575.programs = true := by
  decide_cbv
theorem costSupported_Chunk576_591 : wordCodeCostSupported Chunk576_591.programs = true := by
  decide_cbv
theorem costSupported_Chunk592_607 : wordCodeCostSupported Chunk592_607.programs = true := by
  decide_cbv
theorem costSupported_Chunk608_623 : wordCodeCostSupported Chunk608_623.programs = true := by
  decide_cbv
theorem costSupported_Chunk624_639 : wordCodeCostSupported Chunk624_639.programs = true := by
  decide_cbv
theorem costSupported_Chunk640_655 : wordCodeCostSupported Chunk640_655.programs = true := by
  decide_cbv
theorem costSupported_Chunk656_671 : wordCodeCostSupported Chunk656_671.programs = true := by
  decide_cbv
theorem costSupported_Chunk672_687 : wordCodeCostSupported Chunk672_687.programs = true := by
  decide_cbv
theorem costSupported_Chunk688_703 : wordCodeCostSupported Chunk688_703.programs = true := by
  decide_cbv
theorem costSupported_Chunk704_719 : wordCodeCostSupported Chunk704_719.programs = true := by
  decide_cbv
theorem costSupported_Chunk720_735 : wordCodeCostSupported Chunk720_735.programs = true := by
  decide_cbv
theorem costSupported_Chunk736_751 : wordCodeCostSupported Chunk736_751.programs = true := by
  decide_cbv
theorem costSupported_Chunk752_767 : wordCodeCostSupported Chunk752_767.programs = true := by
  decide_cbv
theorem costSupported_Chunk768_783 : wordCodeCostSupported Chunk768_783.programs = true := by
  decide_cbv
theorem costSupported_Chunk784_799 : wordCodeCostSupported Chunk784_799.programs = true := by
  decide_cbv
theorem costSupported_Chunk800_815 : wordCodeCostSupported Chunk800_815.programs = true := by
  decide_cbv
theorem costSupported_Chunk816_831 : wordCodeCostSupported Chunk816_831.programs = true := by
  decide_cbv
theorem costSupported_Chunk832_847 : wordCodeCostSupported Chunk832_847.programs = true := by
  decide_cbv
theorem costSupported_Chunk848_863 : wordCodeCostSupported Chunk848_863.programs = true := by
  decide_cbv
theorem costSupported_Chunk864_879 : wordCodeCostSupported Chunk864_879.programs = true := by
  decide_cbv
theorem costSupported_Chunk880_889 : wordCodeCostSupported Chunk880_889.programs = true := by
  decide_cbv

/-- Kernel certificates cover all 826 actual allocated Word procedures,
including shared-memory operations and both call continuation branches. -/
theorem guest_word_cost_supported : wordCodeCostSupported Native.programs0 = true := by
  simp only [Native.programs0, Native.programs1, Native.programs2, Native.programs3, Native.programs4, Native.programs5, Native.programs6, Native.programs7, Native.programs8, Native.programs9, Native.programs10, Native.programs11, Native.programs12, Native.programs13, Native.programs14, Native.programs15, Native.programs16, Native.programs17, Native.programs18, Native.programs19, Native.programs20, Native.programs21, Native.programs22, Native.programs23, Native.programs24, Native.programs25, Native.programs26, Native.programs27, Native.programs28, Native.programs29, Native.programs30, Native.programs31, Native.programs32, Native.programs33, Native.programs34, Native.programs35, Native.programs36, Native.programs37, Native.programs38, Native.programs39, Native.programs40, Native.programs41, Native.programs42, Native.programs43, Native.programs44, Native.programs45, Native.programs46, Native.programs47, Native.programs48, Native.programs49, Native.programs50, Native.programs51, Native.programs52, wordCodeCostSupported_append, costSupported_Chunk80_95, costSupported_Chunk96_111, costSupported_Chunk112_127, costSupported_Chunk128_143, costSupported_Chunk144_159, costSupported_Chunk160_175, costSupported_Chunk176_191, costSupported_Chunk192_207, costSupported_Chunk208_223, costSupported_Chunk224_239, costSupported_Chunk240_255, costSupported_Chunk256_271, costSupported_Chunk272_287, costSupported_Chunk288_303, costSupported_Chunk304_319, costSupported_Chunk320_335, costSupported_Chunk336_351, costSupported_Chunk352_367, costSupported_Chunk368_383, costSupported_Chunk384_399, costSupported_Chunk400_415, costSupported_Chunk416_431, costSupported_Chunk432_447, costSupported_Chunk448_463, costSupported_Chunk464_479, costSupported_Chunk480_495, costSupported_Chunk496_511, costSupported_Chunk512_527, costSupported_Chunk528_543, costSupported_Chunk544_559, costSupported_Chunk560_575, costSupported_Chunk576_591, costSupported_Chunk592_607, costSupported_Chunk608_623, costSupported_Chunk624_639, costSupported_Chunk640_655, costSupported_Chunk656_671, costSupported_Chunk672_687, costSupported_Chunk688_703, costSupported_Chunk704_719, costSupported_Chunk720_735, costSupported_Chunk736_751, costSupported_Chunk752_767, costSupported_Chunk768_783, costSupported_Chunk784_799, costSupported_Chunk800_815, costSupported_Chunk816_831, costSupported_Chunk832_847, costSupported_Chunk848_863, costSupported_Chunk864_879, costSupported_Chunk880_889]
  simpa only [wordCodeCostSupported,Bool.true_and,Bool.and_true,List.all_nil] using costSupported_Chunk64_79

/-- Convert the finite checked declaration table to semantic lookup coverage. -/
theorem CostSupportedCode.of_list (programs : List (Nat × Nat × WordLangProgHOL (BitVec 64)))
    (checked : wordCodeCostSupported programs = true) : CostSupportedCode (sptFromAList programs) := by
  intro key arity program found
  rw [sptLookup_sptFromAList] at found
  exact List.all_eq_true.mp checked (key,arity,program) (sptAListLookup_mem _ _ _ found)

theorem guest_word_code_cost_supported : CostSupportedCode (sptFromAList Native.programs0) :=
  CostSupportedCode.of_list _ guest_word_cost_supported

#print axioms costSupported_Chunk80_95
#print axioms costSupported_Chunk96_111
#print axioms costSupported_Chunk112_127
#print axioms costSupported_Chunk128_143
#print axioms costSupported_Chunk144_159
#print axioms costSupported_Chunk160_175
#print axioms costSupported_Chunk176_191
#print axioms costSupported_Chunk192_207
#print axioms costSupported_Chunk208_223
#print axioms costSupported_Chunk224_239
#print axioms costSupported_Chunk240_255
#print axioms costSupported_Chunk256_271
#print axioms costSupported_Chunk272_287
#print axioms costSupported_Chunk288_303
#print axioms costSupported_Chunk304_319
#print axioms costSupported_Chunk320_335
#print axioms costSupported_Chunk336_351
#print axioms costSupported_Chunk352_367
#print axioms costSupported_Chunk368_383
#print axioms costSupported_Chunk384_399
#print axioms costSupported_Chunk400_415
#print axioms costSupported_Chunk416_431
#print axioms costSupported_Chunk432_447
#print axioms costSupported_Chunk448_463
#print axioms costSupported_Chunk464_479
#print axioms costSupported_Chunk480_495
#print axioms costSupported_Chunk496_511
#print axioms costSupported_Chunk512_527
#print axioms costSupported_Chunk528_543
#print axioms costSupported_Chunk544_559
#print axioms costSupported_Chunk560_575
#print axioms costSupported_Chunk576_591
#print axioms costSupported_Chunk592_607
#print axioms costSupported_Chunk608_623
#print axioms costSupported_Chunk624_639
#print axioms costSupported_Chunk640_655
#print axioms costSupported_Chunk656_671
#print axioms costSupported_Chunk672_687
#print axioms costSupported_Chunk688_703
#print axioms costSupported_Chunk704_719
#print axioms costSupported_Chunk720_735
#print axioms costSupported_Chunk736_751
#print axioms costSupported_Chunk752_767
#print axioms costSupported_Chunk768_783
#print axioms costSupported_Chunk784_799
#print axioms costSupported_Chunk800_815
#print axioms costSupported_Chunk816_831
#print axioms costSupported_Chunk832_847
#print axioms costSupported_Chunk848_863
#print axioms costSupported_Chunk864_879
#print axioms costSupported_Chunk880_889
#print axioms guest_word_cost_supported
#print axioms guest_word_code_cost_supported
end InitECandidate.Runtime.WordToStack
