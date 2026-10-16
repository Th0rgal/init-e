import InitECandidate.Runtime.AllocationFree
import InitECandidate.Proofs.BackendStages.Raw
namespace InitECandidate.Runtime.StackAlloc
open InitECandidate.Proofs.BackendStages
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
theorem free_RawStubs : allocationFreeCode RawStubs = true := by
  decide_cbv
theorem free_RawChunk64_79 : allocationFreeCode RawChunk64_79.bodies = true := by
  decide_cbv
theorem free_RawChunk80_95 : allocationFreeCode RawChunk80_95.bodies = true := by
  decide_cbv
theorem free_RawChunk96_111 : allocationFreeCode RawChunk96_111.bodies = true := by
  decide_cbv
theorem free_RawChunk112_127 : allocationFreeCode RawChunk112_127.bodies = true := by
  decide_cbv
theorem free_RawChunk128_143 : allocationFreeCode RawChunk128_143.bodies = true := by
  decide_cbv
theorem free_RawChunk144_159 : allocationFreeCode RawChunk144_159.bodies = true := by
  decide_cbv
theorem free_RawChunk160_175 : allocationFreeCode RawChunk160_175.bodies = true := by
  decide_cbv
theorem free_RawChunk176_191 : allocationFreeCode RawChunk176_191.bodies = true := by
  decide_cbv
theorem free_RawChunk192_207 : allocationFreeCode RawChunk192_207.bodies = true := by
  decide_cbv
theorem free_RawChunk208_223 : allocationFreeCode RawChunk208_223.bodies = true := by
  decide_cbv
theorem free_RawChunk224_239 : allocationFreeCode RawChunk224_239.bodies = true := by
  decide_cbv
theorem free_RawChunk240_255 : allocationFreeCode RawChunk240_255.bodies = true := by
  decide_cbv
theorem free_RawChunk256_271 : allocationFreeCode RawChunk256_271.bodies = true := by
  decide_cbv
theorem free_RawChunk272_287 : allocationFreeCode RawChunk272_287.bodies = true := by
  decide_cbv
theorem free_RawChunk288_303 : allocationFreeCode RawChunk288_303.bodies = true := by
  decide_cbv
theorem free_RawChunk304_319 : allocationFreeCode RawChunk304_319.bodies = true := by
  decide_cbv
theorem free_RawChunk320_335 : allocationFreeCode RawChunk320_335.bodies = true := by
  decide_cbv
theorem free_RawChunk336_351 : allocationFreeCode RawChunk336_351.bodies = true := by
  decide_cbv
theorem free_RawChunk352_367 : allocationFreeCode RawChunk352_367.bodies = true := by
  decide_cbv
theorem free_RawChunk368_383 : allocationFreeCode RawChunk368_383.bodies = true := by
  decide_cbv
theorem free_RawChunk384_399 : allocationFreeCode RawChunk384_399.bodies = true := by
  decide_cbv
theorem free_RawChunk400_415 : allocationFreeCode RawChunk400_415.bodies = true := by
  decide_cbv
theorem free_RawChunk416_431 : allocationFreeCode RawChunk416_431.bodies = true := by
  decide_cbv
theorem free_RawChunk432_447 : allocationFreeCode RawChunk432_447.bodies = true := by
  decide_cbv
theorem free_RawChunk448_463 : allocationFreeCode RawChunk448_463.bodies = true := by
  decide_cbv
theorem free_RawChunk464_479 : allocationFreeCode RawChunk464_479.bodies = true := by
  decide_cbv
theorem free_RawChunk480_495 : allocationFreeCode RawChunk480_495.bodies = true := by
  decide_cbv
theorem free_RawChunk496_511 : allocationFreeCode RawChunk496_511.bodies = true := by
  decide_cbv
theorem free_RawChunk512_527 : allocationFreeCode RawChunk512_527.bodies = true := by
  decide_cbv
theorem free_RawChunk528_543 : allocationFreeCode RawChunk528_543.bodies = true := by
  decide_cbv
theorem free_RawChunk544_559 : allocationFreeCode RawChunk544_559.bodies = true := by
  decide_cbv
theorem free_RawChunk560_575 : allocationFreeCode RawChunk560_575.bodies = true := by
  decide_cbv
theorem free_RawChunk576_591 : allocationFreeCode RawChunk576_591.bodies = true := by
  decide_cbv
theorem free_RawChunk592_607 : allocationFreeCode RawChunk592_607.bodies = true := by
  decide_cbv
theorem free_RawChunk608_623 : allocationFreeCode RawChunk608_623.bodies = true := by
  decide_cbv
theorem free_RawChunk624_639 : allocationFreeCode RawChunk624_639.bodies = true := by
  decide_cbv
theorem free_RawChunk640_655 : allocationFreeCode RawChunk640_655.bodies = true := by
  decide_cbv
theorem free_RawChunk656_671 : allocationFreeCode RawChunk656_671.bodies = true := by
  decide_cbv
theorem free_RawChunk672_687 : allocationFreeCode RawChunk672_687.bodies = true := by
  decide_cbv
theorem free_RawChunk688_703 : allocationFreeCode RawChunk688_703.bodies = true := by
  decide_cbv
theorem free_RawChunk704_719 : allocationFreeCode RawChunk704_719.bodies = true := by
  decide_cbv
theorem free_RawChunk720_735 : allocationFreeCode RawChunk720_735.bodies = true := by
  decide_cbv
theorem free_RawChunk736_751 : allocationFreeCode RawChunk736_751.bodies = true := by
  decide_cbv
theorem free_RawChunk752_767 : allocationFreeCode RawChunk752_767.bodies = true := by
  decide_cbv
theorem free_RawChunk768_783 : allocationFreeCode RawChunk768_783.bodies = true := by
  decide_cbv
theorem free_RawChunk784_799 : allocationFreeCode RawChunk784_799.bodies = true := by
  decide_cbv
theorem free_RawChunk800_815 : allocationFreeCode RawChunk800_815.bodies = true := by
  decide_cbv
theorem free_RawChunk816_831 : allocationFreeCode RawChunk816_831.bodies = true := by
  decide_cbv
theorem free_RawChunk832_847 : allocationFreeCode RawChunk832_847.bodies = true := by
  decide_cbv
theorem free_RawChunk848_863 : allocationFreeCode RawChunk848_863.bodies = true := by
  decide_cbv
theorem free_RawChunk864_879 : allocationFreeCode RawChunk864_879.bodies = true := by
  decide_cbv
theorem free_RawChunk880_889 : allocationFreeCode RawChunk880_889.bodies = true := by
  decide_cbv
theorem actual_allocationFree : allocationFreeCode Raw.stack = true := by
  simp only [Raw.stack, Raw.bodies52, Raw.bodies51, Raw.bodies50, Raw.bodies49, Raw.bodies48, Raw.bodies47, Raw.bodies46, Raw.bodies45, Raw.bodies44, Raw.bodies43, Raw.bodies42, Raw.bodies41, Raw.bodies40, Raw.bodies39, Raw.bodies38, Raw.bodies37, Raw.bodies36, Raw.bodies35, Raw.bodies34, Raw.bodies33, Raw.bodies32, Raw.bodies31, Raw.bodies30, Raw.bodies29, Raw.bodies28, Raw.bodies27, Raw.bodies26, Raw.bodies25, Raw.bodies24, Raw.bodies23, Raw.bodies22, Raw.bodies21, Raw.bodies20, Raw.bodies19, Raw.bodies18, Raw.bodies17, Raw.bodies16, Raw.bodies15, Raw.bodies14, Raw.bodies13, Raw.bodies12, Raw.bodies11, Raw.bodies10, Raw.bodies9, Raw.bodies8, Raw.bodies7, Raw.bodies6, Raw.bodies5, Raw.bodies4, Raw.bodies3, Raw.bodies2, Raw.bodies1, Raw.bodies0, allocationFreeCode_append, free_RawStubs, free_RawChunk64_79, free_RawChunk80_95, free_RawChunk96_111, free_RawChunk112_127, free_RawChunk128_143, free_RawChunk144_159, free_RawChunk160_175, free_RawChunk176_191, free_RawChunk192_207, free_RawChunk208_223, free_RawChunk224_239, free_RawChunk240_255, free_RawChunk256_271, free_RawChunk272_287, free_RawChunk288_303, free_RawChunk304_319, free_RawChunk320_335, free_RawChunk336_351, free_RawChunk352_367, free_RawChunk368_383, free_RawChunk384_399, free_RawChunk400_415, free_RawChunk416_431, free_RawChunk432_447, free_RawChunk448_463, free_RawChunk464_479, free_RawChunk480_495, free_RawChunk496_511, free_RawChunk512_527, free_RawChunk528_543, free_RawChunk544_559, free_RawChunk560_575, free_RawChunk576_591, free_RawChunk592_607, free_RawChunk608_623, free_RawChunk624_639, free_RawChunk640_655, free_RawChunk656_671, free_RawChunk672_687, free_RawChunk688_703, free_RawChunk704_719, free_RawChunk720_735, free_RawChunk736_751, free_RawChunk752_767, free_RawChunk768_783, free_RawChunk784_799, free_RawChunk800_815, free_RawChunk816_831, free_RawChunk832_847, free_RawChunk848_863, free_RawChunk864_879, free_RawChunk880_889]
  rfl
theorem actual_allocation_map : Raw.stack.map Flapjack.Compiler.Backend.StackAlloc.progComp = Raw.stack :=
  allocationFreeCode_map _ actual_allocationFree
#print axioms actual_allocation_map
end InitECandidate.Runtime.StackAlloc
