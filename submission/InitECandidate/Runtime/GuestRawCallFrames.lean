import InitECandidate.Runtime.GuestRawCallFramesFirst
import InitECandidate.Proofs.BackendStages.Native
namespace InitECandidate.Runtime.StackRawCall
open InitECandidate.Proofs.BackendStages
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 100000000

theorem rawFrames_Chunk80_95 : rawCallCodeFramesSupported Chunk80_95.bodies = true := by
  decide_cbv
theorem rawFrames_Chunk96_111 : rawCallCodeFramesSupported Chunk96_111.bodies = true := by
  decide_cbv
theorem rawFrames_Chunk112_127 : rawCallCodeFramesSupported Chunk112_127.bodies = true := by
  decide_cbv
theorem rawFrames_Chunk128_143 : rawCallCodeFramesSupported Chunk128_143.bodies = true := by
  decide_cbv
theorem rawFrames_Chunk144_159 : rawCallCodeFramesSupported Chunk144_159.bodies = true := by
  decide_cbv
theorem rawFrames_Chunk160_175 : rawCallCodeFramesSupported Chunk160_175.bodies = true := by
  decide_cbv
theorem rawFrames_Chunk176_191 : rawCallCodeFramesSupported Chunk176_191.bodies = true := by
  decide_cbv
theorem rawFrames_Chunk192_207 : rawCallCodeFramesSupported Chunk192_207.bodies = true := by
  decide_cbv
theorem rawFrames_Chunk208_223 : rawCallCodeFramesSupported Chunk208_223.bodies = true := by
  decide_cbv
theorem rawFrames_Chunk224_239 : rawCallCodeFramesSupported Chunk224_239.bodies = true := by
  decide_cbv
theorem rawFrames_Chunk240_255 : rawCallCodeFramesSupported Chunk240_255.bodies = true := by
  decide_cbv
theorem rawFrames_Chunk256_271 : rawCallCodeFramesSupported Chunk256_271.bodies = true := by
  decide_cbv
theorem rawFrames_Chunk272_287 : rawCallCodeFramesSupported Chunk272_287.bodies = true := by
  decide_cbv
theorem rawFrames_Chunk288_303 : rawCallCodeFramesSupported Chunk288_303.bodies = true := by
  decide_cbv
theorem rawFrames_Chunk304_319 : rawCallCodeFramesSupported Chunk304_319.bodies = true := by
  decide_cbv
theorem rawFrames_Chunk320_335 : rawCallCodeFramesSupported Chunk320_335.bodies = true := by
  decide_cbv
theorem rawFrames_Chunk336_351 : rawCallCodeFramesSupported Chunk336_351.bodies = true := by
  decide_cbv
theorem rawFrames_Chunk352_367 : rawCallCodeFramesSupported Chunk352_367.bodies = true := by
  decide_cbv
theorem rawFrames_Chunk368_383 : rawCallCodeFramesSupported Chunk368_383.bodies = true := by
  decide_cbv
theorem rawFrames_Chunk384_399 : rawCallCodeFramesSupported Chunk384_399.bodies = true := by
  decide_cbv
theorem rawFrames_Chunk400_415 : rawCallCodeFramesSupported Chunk400_415.bodies = true := by
  decide_cbv
theorem rawFrames_Chunk416_431 : rawCallCodeFramesSupported Chunk416_431.bodies = true := by
  decide_cbv
theorem rawFrames_Chunk432_447 : rawCallCodeFramesSupported Chunk432_447.bodies = true := by
  decide_cbv
theorem rawFrames_Chunk448_463 : rawCallCodeFramesSupported Chunk448_463.bodies = true := by
  decide_cbv
theorem rawFrames_Chunk464_479 : rawCallCodeFramesSupported Chunk464_479.bodies = true := by
  decide_cbv
theorem rawFrames_Chunk480_495 : rawCallCodeFramesSupported Chunk480_495.bodies = true := by
  decide_cbv
theorem rawFrames_Chunk496_511 : rawCallCodeFramesSupported Chunk496_511.bodies = true := by
  decide_cbv
theorem rawFrames_Chunk512_527 : rawCallCodeFramesSupported Chunk512_527.bodies = true := by
  decide_cbv
theorem rawFrames_Chunk528_543 : rawCallCodeFramesSupported Chunk528_543.bodies = true := by
  decide_cbv
theorem rawFrames_Chunk544_559 : rawCallCodeFramesSupported Chunk544_559.bodies = true := by
  decide_cbv
theorem rawFrames_Chunk560_575 : rawCallCodeFramesSupported Chunk560_575.bodies = true := by
  decide_cbv
theorem rawFrames_Chunk576_591 : rawCallCodeFramesSupported Chunk576_591.bodies = true := by
  decide_cbv
theorem rawFrames_Chunk592_607 : rawCallCodeFramesSupported Chunk592_607.bodies = true := by
  decide_cbv
theorem rawFrames_Chunk608_623 : rawCallCodeFramesSupported Chunk608_623.bodies = true := by
  decide_cbv
theorem rawFrames_Chunk624_639 : rawCallCodeFramesSupported Chunk624_639.bodies = true := by
  decide_cbv
theorem rawFrames_Chunk640_655 : rawCallCodeFramesSupported Chunk640_655.bodies = true := by
  decide_cbv
theorem rawFrames_Chunk656_671 : rawCallCodeFramesSupported Chunk656_671.bodies = true := by
  decide_cbv
theorem rawFrames_Chunk672_687 : rawCallCodeFramesSupported Chunk672_687.bodies = true := by
  decide_cbv
theorem rawFrames_Chunk688_703 : rawCallCodeFramesSupported Chunk688_703.bodies = true := by
  decide_cbv
theorem rawFrames_Chunk704_719 : rawCallCodeFramesSupported Chunk704_719.bodies = true := by
  decide_cbv
theorem rawFrames_Chunk720_735 : rawCallCodeFramesSupported Chunk720_735.bodies = true := by
  decide_cbv
theorem rawFrames_Chunk736_751 : rawCallCodeFramesSupported Chunk736_751.bodies = true := by
  decide_cbv
theorem rawFrames_Chunk752_767 : rawCallCodeFramesSupported Chunk752_767.bodies = true := by
  decide_cbv
theorem rawFrames_Chunk768_783 : rawCallCodeFramesSupported Chunk768_783.bodies = true := by
  decide_cbv
theorem rawFrames_Chunk784_799 : rawCallCodeFramesSupported Chunk784_799.bodies = true := by
  decide_cbv
theorem rawFrames_Chunk800_815 : rawCallCodeFramesSupported Chunk800_815.bodies = true := by
  decide_cbv
theorem rawFrames_Chunk816_831 : rawCallCodeFramesSupported Chunk816_831.bodies = true := by
  decide_cbv
theorem rawFrames_Chunk832_847 : rawCallCodeFramesSupported Chunk832_847.bodies = true := by
  decide_cbv
theorem rawFrames_Chunk848_863 : rawCallCodeFramesSupported Chunk848_863.bodies = true := by
  decide_cbv
theorem rawFrames_Chunk864_879 : rawCallCodeFramesSupported Chunk864_879.bodies = true := by
  decide_cbv
theorem rawFrames_Chunk880_889 : rawCallCodeFramesSupported Chunk880_889.bodies = true := by
  decide_cbv

theorem guest_raw_call_body_frames : rawCallCodeFramesSupported Native.bodies0 = true := by
  simp only [
    Native.bodies0, Native.bodies1, Native.bodies2, Native.bodies3, Native.bodies4, Native.bodies5, Native.bodies6, Native.bodies7, Native.bodies8, Native.bodies9, Native.bodies10, Native.bodies11, Native.bodies12, Native.bodies13, Native.bodies14, Native.bodies15, Native.bodies16, Native.bodies17, Native.bodies18, Native.bodies19, Native.bodies20, Native.bodies21, Native.bodies22, Native.bodies23, Native.bodies24, Native.bodies25, Native.bodies26, Native.bodies27, Native.bodies28, Native.bodies29, Native.bodies30, Native.bodies31, Native.bodies32, Native.bodies33, Native.bodies34, Native.bodies35, Native.bodies36, Native.bodies37, Native.bodies38, Native.bodies39, Native.bodies40, Native.bodies41, Native.bodies42, Native.bodies43, Native.bodies44, Native.bodies45, Native.bodies46, Native.bodies47, Native.bodies48, Native.bodies49, Native.bodies50, Native.bodies51, Native.bodies52,
    rawCallCodeFramesSupported_append,
    rawFrames_Chunk64_79, rawFrames_Chunk80_95, rawFrames_Chunk96_111, rawFrames_Chunk112_127, rawFrames_Chunk128_143, rawFrames_Chunk144_159, rawFrames_Chunk160_175, rawFrames_Chunk176_191, rawFrames_Chunk192_207, rawFrames_Chunk208_223, rawFrames_Chunk224_239, rawFrames_Chunk240_255, rawFrames_Chunk256_271, rawFrames_Chunk272_287, rawFrames_Chunk288_303, rawFrames_Chunk304_319, rawFrames_Chunk320_335, rawFrames_Chunk336_351, rawFrames_Chunk352_367, rawFrames_Chunk368_383, rawFrames_Chunk384_399, rawFrames_Chunk400_415, rawFrames_Chunk416_431, rawFrames_Chunk432_447, rawFrames_Chunk448_463, rawFrames_Chunk464_479, rawFrames_Chunk480_495, rawFrames_Chunk496_511, rawFrames_Chunk512_527, rawFrames_Chunk528_543, rawFrames_Chunk544_559, rawFrames_Chunk560_575, rawFrames_Chunk576_591, rawFrames_Chunk592_607, rawFrames_Chunk608_623, rawFrames_Chunk624_639, rawFrames_Chunk640_655, rawFrames_Chunk656_671, rawFrames_Chunk672_687, rawFrames_Chunk688_703, rawFrames_Chunk704_719, rawFrames_Chunk720_735, rawFrames_Chunk736_751, rawFrames_Chunk752_767, rawFrames_Chunk768_783, rawFrames_Chunk784_799, rawFrames_Chunk800_815, rawFrames_Chunk816_831, rawFrames_Chunk832_847, rawFrames_Chunk848_863, rawFrames_Chunk864_879, rawFrames_Chunk880_889,
    Bool.true_and]
  rfl

theorem guest_raw_call_stub_frames : rawCallCodeFramesSupported (Native.stack.take 2) = true := by
  decide_cbv

/-- All actual pre-raw-call code, including stubs, satisfies the frame
conditions funding the optimizer without an extra multiplicative factor. -/
theorem guest_raw_call_frames : rawCallCodeFramesSupported Native.stack = true := by
  rw [show Native.stack = Native.stack.take 2 ++ Native.bodies0 from rfl,
    rawCallCodeFramesSupported_append, guest_raw_call_stub_frames,
    guest_raw_call_body_frames]
  rfl

#print axioms rawFrames_Chunk80_95
#print axioms rawFrames_Chunk96_111
#print axioms rawFrames_Chunk112_127
#print axioms rawFrames_Chunk128_143
#print axioms rawFrames_Chunk144_159
#print axioms rawFrames_Chunk160_175
#print axioms rawFrames_Chunk176_191
#print axioms rawFrames_Chunk192_207
#print axioms rawFrames_Chunk208_223
#print axioms rawFrames_Chunk224_239
#print axioms rawFrames_Chunk240_255
#print axioms rawFrames_Chunk256_271
#print axioms rawFrames_Chunk272_287
#print axioms rawFrames_Chunk288_303
#print axioms rawFrames_Chunk304_319
#print axioms rawFrames_Chunk320_335
#print axioms rawFrames_Chunk336_351
#print axioms rawFrames_Chunk352_367
#print axioms rawFrames_Chunk368_383
#print axioms rawFrames_Chunk384_399
#print axioms rawFrames_Chunk400_415
#print axioms rawFrames_Chunk416_431
#print axioms rawFrames_Chunk432_447
#print axioms rawFrames_Chunk448_463
#print axioms rawFrames_Chunk464_479
#print axioms rawFrames_Chunk480_495
#print axioms rawFrames_Chunk496_511
#print axioms rawFrames_Chunk512_527
#print axioms rawFrames_Chunk528_543
#print axioms rawFrames_Chunk544_559
#print axioms rawFrames_Chunk560_575
#print axioms rawFrames_Chunk576_591
#print axioms rawFrames_Chunk592_607
#print axioms rawFrames_Chunk608_623
#print axioms rawFrames_Chunk624_639
#print axioms rawFrames_Chunk640_655
#print axioms rawFrames_Chunk656_671
#print axioms rawFrames_Chunk672_687
#print axioms rawFrames_Chunk688_703
#print axioms rawFrames_Chunk704_719
#print axioms rawFrames_Chunk720_735
#print axioms rawFrames_Chunk736_751
#print axioms rawFrames_Chunk752_767
#print axioms rawFrames_Chunk768_783
#print axioms rawFrames_Chunk784_799
#print axioms rawFrames_Chunk800_815
#print axioms rawFrames_Chunk816_831
#print axioms rawFrames_Chunk832_847
#print axioms rawFrames_Chunk848_863
#print axioms rawFrames_Chunk864_879
#print axioms rawFrames_Chunk880_889
#print axioms guest_raw_call_body_frames
#print axioms guest_raw_call_stub_frames
#print axioms guest_raw_call_frames
end InitECandidate.Runtime.StackRawCall
