import InitECandidate.Proofs.CompactComputation
import InitECandidate.Proofs.SsaCheckpoints154.Proof8
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
open Flapjack Flapjack.Compiler.Backend
open InitECandidate.Proofs.SmallSsaKernelComputation
namespace InitECandidate.Proofs.SsaCheckpoints154
theorem node576_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_1792 state64 453 state65 = (program30775,state5664,10013) := by
  unfold InitECandidate.Proofs.WordStages.word154_1_1792
  rw [ssaStructural.eq_def]
  dsimp only
  rw [node574_eq, node575_eq]
  kernel_rfl
theorem node577_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_654 state5664 10013 state65 = (program30776,state5677,10017) := by
  kernel_rfl
theorem node578_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_1793 state64 453 state65 = (program30777,state5677,10017) := by
  unfold InitECandidate.Proofs.WordStages.word154_1_1793
  rw [ssaStructural.eq_def]
  dsimp only
  rw [node576_eq, node577_eq]
  kernel_rfl
theorem node579_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_1215 state5677 10017 state65 = (program30838,state5720,10141) := by
  kernel_rfl
theorem node580_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_1794 state64 453 state65 = (program30839,state5720,10141) := by
  unfold InitECandidate.Proofs.WordStages.word154_1_1794
  rw [ssaStructural.eq_def]
  dsimp only
  rw [node578_eq, node579_eq]
  kernel_rfl
theorem node581_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_1825 state5720 10141 state65 = (program30900,state5755,10265) := by
  kernel_rfl
theorem node582_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_1380 state5755 10265 state65 = (program30903,state5774,10273) := by
  kernel_rfl
theorem node583_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_1826 state5720 10141 state65 = (program30904,state5774,10273) := by
  unfold InitECandidate.Proofs.WordStages.word154_1_1826
  rw [ssaStructural.eq_def]
  dsimp only
  rw [node581_eq, node582_eq]
  kernel_rfl
theorem node584_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_590 state5774 10273 state65 = (program30905,state5782,10277) := by
  kernel_rfl
theorem node585_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_1827 state5720 10141 state65 = (program30906,state5782,10277) := by
  unfold InitECandidate.Proofs.WordStages.word154_1_1827
  rw [ssaStructural.eq_def]
  dsimp only
  rw [node583_eq, node584_eq]
  kernel_rfl
theorem node586_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_592 state5782 10277 state65 = (program30907,state5790,10281) := by
  kernel_rfl
theorem node587_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_1828 state5720 10141 state65 = (program30908,state5790,10281) := by
  unfold InitECandidate.Proofs.WordStages.word154_1_1828
  rw [ssaStructural.eq_def]
  dsimp only
  rw [node585_eq, node586_eq]
  kernel_rfl
theorem node588_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_1829 state64 453 state65 = (program30909,state5790,10281) := by
  unfold InitECandidate.Proofs.WordStages.word154_1_1829
  rw [ssaStructural.eq_def]
  dsimp only
  rw [node580_eq, node587_eq]
  kernel_rfl
theorem node589_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_1830 state5790 10281 state65 = (program30910,state5802,10285) := by
  kernel_rfl
theorem node590_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_1831 state64 453 state65 = (program30911,state5802,10285) := by
  unfold InitECandidate.Proofs.WordStages.word154_1_1831
  rw [ssaStructural.eq_def]
  dsimp only
  rw [node588_eq, node589_eq]
  kernel_rfl
theorem node591_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_1834 state5802 10285 state65 = (program30972,state5845,10409) := by
  kernel_rfl
theorem node592_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_1835 state64 453 state65 = (program30973,state5845,10409) := by
  unfold InitECandidate.Proofs.WordStages.word154_1_1835
  rw [ssaStructural.eq_def]
  dsimp only
  rw [node590_eq, node591_eq]
  kernel_rfl
theorem node593_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_1230 state5845 10409 state65 = (program30982,state5868,10429) := by
  kernel_rfl
theorem node594_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_1836 state64 453 state65 = (program30983,state5868,10429) := by
  unfold InitECandidate.Proofs.WordStages.word154_1_1836
  rw [ssaStructural.eq_def]
  dsimp only
  rw [node592_eq, node593_eq]
  kernel_rfl
theorem node595_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_740 state5868 10429 state65 = (program30984,state5880,10433) := by
  kernel_rfl
theorem node596_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_1837 state64 453 state65 = (program30985,state5880,10433) := by
  unfold InitECandidate.Proofs.WordStages.word154_1_1837
  rw [ssaStructural.eq_def]
  dsimp only
  rw [node594_eq, node595_eq]
  kernel_rfl
theorem node597_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_1240 state5880 10433 state65 = (program31046,state5922,10557) := by
  kernel_rfl
theorem node598_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_1838 state64 453 state65 = (program31047,state5922,10557) := by
  unfold InitECandidate.Proofs.WordStages.word154_1_1838
  rw [ssaStructural.eq_def]
  dsimp only
  rw [node596_eq, node597_eq]
  kernel_rfl
theorem node599_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_1869 state5922 10557 state65 = (program31108,state5955,10681) := by
  kernel_rfl
theorem node600_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_1432 state5955 10681 state65 = (program31111,state5975,10689) := by
  kernel_rfl
theorem node601_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_1870 state5922 10557 state65 = (program31112,state5975,10689) := by
  unfold InitECandidate.Proofs.WordStages.word154_1_1870
  rw [ssaStructural.eq_def]
  dsimp only
  rw [node599_eq, node600_eq]
  kernel_rfl
theorem node602_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_590 state5975 10689 state65 = (program31113,state5983,10693) := by
  kernel_rfl
theorem node603_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_1871 state5922 10557 state65 = (program31114,state5983,10693) := by
  unfold InitECandidate.Proofs.WordStages.word154_1_1871
  rw [ssaStructural.eq_def]
  dsimp only
  rw [node601_eq, node602_eq]
  kernel_rfl
theorem node604_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_592 state5983 10693 state65 = (program31115,state5991,10697) := by
  kernel_rfl
theorem node605_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_1872 state5922 10557 state65 = (program31116,state5991,10697) := by
  unfold InitECandidate.Proofs.WordStages.word154_1_1872
  rw [ssaStructural.eq_def]
  dsimp only
  rw [node603_eq, node604_eq]
  kernel_rfl
theorem node606_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_1873 state64 453 state65 = (program31117,state5991,10697) := by
  unfold InitECandidate.Proofs.WordStages.word154_1_1873
  rw [ssaStructural.eq_def]
  dsimp only
  rw [node598_eq, node605_eq]
  kernel_rfl
theorem node607_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_1874 state5991 10697 state65 = (program31118,state6004,10701) := by
  kernel_rfl
theorem node608_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_1875 state64 453 state65 = (program31119,state6004,10701) := by
  unfold InitECandidate.Proofs.WordStages.word154_1_1875
  rw [ssaStructural.eq_def]
  dsimp only
  rw [node606_eq, node607_eq]
  kernel_rfl
theorem node609_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_1878 state6004 10701 state65 = (program31180,state6049,10825) := by
  kernel_rfl
theorem node610_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_1879 state64 453 state65 = (program31181,state6049,10825) := by
  unfold InitECandidate.Proofs.WordStages.word154_1_1879
  rw [ssaStructural.eq_def]
  dsimp only
  rw [node608_eq, node609_eq]
  kernel_rfl
theorem node611_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_1252 state6049 10825 state65 = (program31190,state6072,10845) := by
  kernel_rfl
theorem node612_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_1880 state64 453 state65 = (program31191,state6072,10845) := by
  unfold InitECandidate.Proofs.WordStages.word154_1_1880
  rw [ssaStructural.eq_def]
  dsimp only
  rw [node610_eq, node611_eq]
  kernel_rfl
theorem node613_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_813 state6072 10845 state65 = (program31192,state6082,10849) := by
  kernel_rfl
theorem node614_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_1881 state64 453 state65 = (program31193,state6082,10849) := by
  unfold InitECandidate.Proofs.WordStages.word154_1_1881
  rw [ssaStructural.eq_def]
  dsimp only
  rw [node612_eq, node613_eq]
  kernel_rfl
theorem node615_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_846 state6082 10849 state65 = (program31254,state6124,10973) := by
  kernel_rfl
theorem node616_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_1882 state64 453 state65 = (program31255,state6124,10973) := by
  unfold InitECandidate.Proofs.WordStages.word154_1_1882
  rw [ssaStructural.eq_def]
  dsimp only
  rw [node614_eq, node615_eq]
  kernel_rfl
theorem node617_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_1913 state6124 10973 state65 = (program31316,state6160,11097) := by
  kernel_rfl
theorem node618_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_1483 state6160 11097 state65 = (program31319,state6179,11105) := by
  kernel_rfl
theorem node619_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_1914 state6124 10973 state65 = (program31320,state6179,11105) := by
  unfold InitECandidate.Proofs.WordStages.word154_1_1914
  rw [ssaStructural.eq_def]
  dsimp only
  rw [node617_eq, node618_eq]
  kernel_rfl
theorem node620_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_590 state6179 11105 state65 = (program31321,state6187,11109) := by
  kernel_rfl
theorem node621_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_1915 state6124 10973 state65 = (program31322,state6187,11109) := by
  unfold InitECandidate.Proofs.WordStages.word154_1_1915
  rw [ssaStructural.eq_def]
  dsimp only
  rw [node619_eq, node620_eq]
  kernel_rfl
theorem node622_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_592 state6187 11109 state65 = (program31323,state6195,11113) := by
  kernel_rfl
theorem node623_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_1916 state6124 10973 state65 = (program31324,state6195,11113) := by
  unfold InitECandidate.Proofs.WordStages.word154_1_1916
  rw [ssaStructural.eq_def]
  dsimp only
  rw [node621_eq, node622_eq]
  kernel_rfl
theorem node624_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_1917 state64 453 state65 = (program31325,state6195,11113) := by
  unfold InitECandidate.Proofs.WordStages.word154_1_1917
  rw [ssaStructural.eq_def]
  dsimp only
  rw [node616_eq, node623_eq]
  kernel_rfl
theorem node625_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_1918 state6195 11113 state65 = (program31326,state6207,11117) := by
  kernel_rfl
theorem node626_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_1919 state64 453 state65 = (program31327,state6207,11117) := by
  unfold InitECandidate.Proofs.WordStages.word154_1_1919
  rw [ssaStructural.eq_def]
  dsimp only
  rw [node624_eq, node625_eq]
  kernel_rfl
theorem node627_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_1922 state6207 11117 state65 = (program31388,state6249,11241) := by
  kernel_rfl
theorem node628_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_1923 state64 453 state65 = (program31389,state6249,11241) := by
  unfold InitECandidate.Proofs.WordStages.word154_1_1923
  rw [ssaStructural.eq_def]
  dsimp only
  rw [node626_eq, node627_eq]
  kernel_rfl
theorem node629_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_886 state6249 11241 state65 = (program31398,state6275,11261) := by
  kernel_rfl
theorem node630_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_1924 state64 453 state65 = (program31399,state6275,11261) := by
  unfold InitECandidate.Proofs.WordStages.word154_1_1924
  rw [ssaStructural.eq_def]
  dsimp only
  rw [node628_eq, node629_eq]
  kernel_rfl
theorem node631_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_888 state6275 11261 state65 = (program31400,state6288,11265) := by
  kernel_rfl
theorem node632_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_1925 state64 453 state65 = (program31401,state6288,11265) := by
  unfold InitECandidate.Proofs.WordStages.word154_1_1925
  rw [ssaStructural.eq_def]
  dsimp only
  rw [node630_eq, node631_eq]
  kernel_rfl
theorem node633_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_922 state6288 11265 state65 = (program31462,state6328,11389) := by
  kernel_rfl
theorem node634_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_1926 state64 453 state65 = (program31463,state6328,11389) := by
  unfold InitECandidate.Proofs.WordStages.word154_1_1926
  rw [ssaStructural.eq_def]
  dsimp only
  rw [node632_eq, node633_eq]
  kernel_rfl
theorem node635_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_1956 state6328 11389 state65 = (program31524,state6366,11513) := by
  kernel_rfl
theorem node636_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_1532 state6366 11513 state65 = (program31527,state6386,11521) := by
  kernel_rfl
theorem node637_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_1957 state6328 11389 state65 = (program31528,state6386,11521) := by
  unfold InitECandidate.Proofs.WordStages.word154_1_1957
  rw [ssaStructural.eq_def]
  dsimp only
  rw [node635_eq, node636_eq]
  kernel_rfl
theorem node638_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_590 state6386 11521 state65 = (program31529,state6394,11525) := by
  kernel_rfl
theorem node639_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_1958 state6328 11389 state65 = (program31530,state6394,11525) := by
  unfold InitECandidate.Proofs.WordStages.word154_1_1958
  rw [ssaStructural.eq_def]
  dsimp only
  rw [node637_eq, node638_eq]
  kernel_rfl
end InitECandidate.Proofs.SsaCheckpoints154
