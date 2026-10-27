import InitECandidate.Proofs.CompactComputation
import InitECandidate.Proofs.SsaCheckpoints154.Proof3
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
open Flapjack Flapjack.Compiler.Backend
open InitECandidate.Proofs.SmallSsaKernelComputation
namespace InitECandidate.Proofs.SsaCheckpoints154
theorem node256_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_562 state64 453 state65 = (program26726,state1759,1853) := by
  unfold InitECandidate.Proofs.WordStages.word154_1_562
  rw [ssaStructural.eq_def]
  dsimp only
  rw [node254_eq, node255_eq]
  kernel_rfl
theorem node257_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_563 state1759 1853 state65 = (InitECandidate.Proofs.WordStages.word154_2_819,state1765,1857) := by
  kernel_rfl
theorem node258_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_564 state64 453 state65 = (program26727,state1765,1857) := by
  unfold InitECandidate.Proofs.WordStages.word154_1_564
  rw [ssaStructural.eq_def]
  dsimp only
  rw [node256_eq, node257_eq]
  kernel_rfl
theorem node259_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_565 state1765 1857 state65 = (program26728,state1773,1861) := by
  kernel_rfl
theorem node260_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_566 state64 453 state65 = (program26729,state1773,1861) := by
  unfold InitECandidate.Proofs.WordStages.word154_1_566
  rw [ssaStructural.eq_def]
  dsimp only
  rw [node258_eq, node259_eq]
  kernel_rfl
theorem node261_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_567 state1773 1861 state65 = (program26730,state1780,1865) := by
  kernel_rfl
theorem node262_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_568 state64 453 state65 = (program26731,state1780,1865) := by
  unfold InitECandidate.Proofs.WordStages.word154_1_568
  rw [ssaStructural.eq_def]
  dsimp only
  rw [node260_eq, node261_eq]
  kernel_rfl
theorem node263_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_569 state1780 1865 state65 = (program26732,state1788,1869) := by
  kernel_rfl
theorem node264_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_570 state64 453 state65 = (program26733,state1788,1869) := by
  unfold InitECandidate.Proofs.WordStages.word154_1_570
  rw [ssaStructural.eq_def]
  dsimp only
  rw [node262_eq, node263_eq]
  kernel_rfl
theorem node265_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_571 state1788 1869 state65 = (program26734,state1793,1873) := by
  kernel_rfl
theorem node266_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_572 state64 453 state65 = (program26735,state1793,1873) := by
  unfold InitECandidate.Proofs.WordStages.word154_1_572
  rw [ssaStructural.eq_def]
  dsimp only
  rw [node264_eq, node265_eq]
  kernel_rfl
theorem node267_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_573 state1793 1873 state65 = (program26736,state1800,1877) := by
  kernel_rfl
theorem node268_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_574 state64 453 state65 = (program26737,state1800,1877) := by
  unfold InitECandidate.Proofs.WordStages.word154_1_574
  rw [ssaStructural.eq_def]
  dsimp only
  rw [node266_eq, node267_eq]
  kernel_rfl
theorem node269_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_575 state1800 1877 state65 = (program26738,state1807,1881) := by
  kernel_rfl
theorem node270_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_576 state64 453 state65 = (program26739,state1807,1881) := by
  unfold InitECandidate.Proofs.WordStages.word154_1_576
  rw [ssaStructural.eq_def]
  dsimp only
  rw [node268_eq, node269_eq]
  kernel_rfl
theorem node271_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_577 state1807 1881 state65 = (program26740,state1815,1885) := by
  kernel_rfl
theorem node272_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_578 state64 453 state65 = (program26741,state1815,1885) := by
  unfold InitECandidate.Proofs.WordStages.word154_1_578
  rw [ssaStructural.eq_def]
  dsimp only
  rw [node270_eq, node271_eq]
  kernel_rfl
theorem node273_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_583 state1815 1885 state65 = (program26746,state1833,1897) := by
  kernel_rfl
theorem node274_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_584 state64 453 state65 = (program26747,state1833,1897) := by
  unfold InitECandidate.Proofs.WordStages.word154_1_584
  rw [ssaStructural.eq_def]
  dsimp only
  rw [node272_eq, node273_eq]
  kernel_rfl
theorem node275_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_593 state1833 1897 state65 = (program26756,state1854,1917) := by
  kernel_rfl
theorem node276_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_594 state64 453 state65 = (program26757,state1854,1917) := by
  unfold InitECandidate.Proofs.WordStages.word154_1_594
  rw [ssaStructural.eq_def]
  dsimp only
  rw [node274_eq, node275_eq]
  kernel_rfl
theorem node277_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_595 state1854 1917 state65 = (program26758,state1867,1921) := by
  kernel_rfl
theorem node278_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_596 state64 453 state65 = (program26759,state1867,1921) := by
  unfold InitECandidate.Proofs.WordStages.word154_1_596
  rw [ssaStructural.eq_def]
  dsimp only
  rw [node276_eq, node277_eq]
  kernel_rfl
theorem node279_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_602 state1867 1921 state65 = (program26768,state1891,1941) := by
  kernel_rfl
theorem node280_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_603 state64 453 state65 = (program26769,state1891,1941) := by
  unfold InitECandidate.Proofs.WordStages.word154_1_603
  rw [ssaStructural.eq_def]
  dsimp only
  rw [node278_eq, node279_eq]
  kernel_rfl
theorem node281_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_646 state1891 1941 state65 = (program26821,state1928,2049) := by
  kernel_rfl
theorem node282_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_647 state64 453 state65 = (program26822,state1928,2049) := by
  unfold InitECandidate.Proofs.WordStages.word154_1_647
  rw [ssaStructural.eq_def]
  dsimp only
  rw [node280_eq, node281_eq]
  kernel_rfl
theorem node283_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_652 state1928 2049 state65 = (program26831,state1949,2069) := by
  kernel_rfl
theorem node284_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_653 state64 453 state65 = (program26832,state1949,2069) := by
  unfold InitECandidate.Proofs.WordStages.word154_1_653
  rw [ssaStructural.eq_def]
  dsimp only
  rw [node282_eq, node283_eq]
  kernel_rfl
theorem node285_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_654 state1949 2069 state65 = (program26833,state1962,2073) := by
  kernel_rfl
theorem node286_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_655 state64 453 state65 = (program26834,state1962,2073) := by
  unfold InitECandidate.Proofs.WordStages.word154_1_655
  rw [ssaStructural.eq_def]
  dsimp only
  rw [node284_eq, node285_eq]
  kernel_rfl
theorem node287_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_698 state1962 2073 state65 = (program26885,state2000,2189) := by
  kernel_rfl
theorem node288_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_699 state64 453 state65 = (program26886,state2000,2189) := by
  unfold InitECandidate.Proofs.WordStages.word154_1_699
  rw [ssaStructural.eq_def]
  dsimp only
  rw [node286_eq, node287_eq]
  kernel_rfl
theorem node289_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_732 state2000 2189 state65 = (program26940,state2039,2305) := by
  kernel_rfl
theorem node290_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_733 state64 453 state65 = (program26941,state2039,2305) := by
  unfold InitECandidate.Proofs.WordStages.word154_1_733
  rw [ssaStructural.eq_def]
  dsimp only
  rw [node288_eq, node289_eq]
  kernel_rfl
theorem node291_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_738 state2039 2305 state65 = (program26950,state2060,2325) := by
  kernel_rfl
theorem node292_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_739 state64 453 state65 = (program26951,state2060,2325) := by
  unfold InitECandidate.Proofs.WordStages.word154_1_739
  rw [ssaStructural.eq_def]
  dsimp only
  rw [node290_eq, node291_eq]
  kernel_rfl
theorem node293_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_740 state2060 2325 state65 = (program26952,state2072,2329) := by
  kernel_rfl
theorem node294_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_741 state64 453 state65 = (program26953,state2072,2329) := by
  unfold InitECandidate.Proofs.WordStages.word154_1_741
  rw [ssaStructural.eq_def]
  dsimp only
  rw [node292_eq, node293_eq]
  kernel_rfl
theorem node295_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_772 state2072 2329 state65 = (program27009,state2113,2453) := by
  kernel_rfl
theorem node296_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_773 state64 453 state65 = (program27010,state2113,2453) := by
  unfold InitECandidate.Proofs.WordStages.word154_1_773
  rw [ssaStructural.eq_def]
  dsimp only
  rw [node294_eq, node295_eq]
  kernel_rfl
theorem node297_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_806 state2113 2453 state65 = (program27064,state2156,2569) := by
  kernel_rfl
theorem node298_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_807 state64 453 state65 = (program27065,state2156,2569) := by
  unfold InitECandidate.Proofs.WordStages.word154_1_807
  rw [ssaStructural.eq_def]
  dsimp only
  rw [node296_eq, node297_eq]
  kernel_rfl
theorem node299_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_811 state2156 2569 state65 = (program27074,state2177,2589) := by
  kernel_rfl
theorem node300_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_812 state64 453 state65 = (program27075,state2177,2589) := by
  unfold InitECandidate.Proofs.WordStages.word154_1_812
  rw [ssaStructural.eq_def]
  dsimp only
  rw [node298_eq, node299_eq]
  kernel_rfl
theorem node301_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_813 state2177 2589 state65 = (program27076,state2187,2593) := by
  kernel_rfl
theorem node302_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_814 state64 453 state65 = (program27077,state2187,2593) := by
  unfold InitECandidate.Proofs.WordStages.word154_1_814
  rw [ssaStructural.eq_def]
  dsimp only
  rw [node300_eq, node301_eq]
  kernel_rfl
theorem node303_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_846 state2187 2593 state65 = (program27137,state2229,2717) := by
  kernel_rfl
theorem node304_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_847 state64 453 state65 = (program27138,state2229,2717) := by
  unfold InitECandidate.Proofs.WordStages.word154_1_847
  rw [ssaStructural.eq_def]
  dsimp only
  rw [node302_eq, node303_eq]
  kernel_rfl
theorem node305_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_881 state2229 2717 state65 = (program27199,state2271,2841) := by
  kernel_rfl
theorem node306_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_882 state64 453 state65 = (program27200,state2271,2841) := by
  unfold InitECandidate.Proofs.WordStages.word154_1_882
  rw [ssaStructural.eq_def]
  dsimp only
  rw [node304_eq, node305_eq]
  kernel_rfl
theorem node307_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_886 state2271 2841 state65 = (program27209,state2297,2861) := by
  kernel_rfl
theorem node308_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_887 state64 453 state65 = (program27210,state2297,2861) := by
  unfold InitECandidate.Proofs.WordStages.word154_1_887
  rw [ssaStructural.eq_def]
  dsimp only
  rw [node306_eq, node307_eq]
  kernel_rfl
theorem node309_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_888 state2297 2861 state65 = (program27211,state2310,2865) := by
  kernel_rfl
theorem node310_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_889 state64 453 state65 = (program27212,state2310,2865) := by
  unfold InitECandidate.Proofs.WordStages.word154_1_889
  rw [ssaStructural.eq_def]
  dsimp only
  rw [node308_eq, node309_eq]
  kernel_rfl
theorem node311_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_922 state2310 2865 state65 = (program27272,state2350,2989) := by
  kernel_rfl
theorem node312_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_923 state64 453 state65 = (program27273,state2350,2989) := by
  unfold InitECandidate.Proofs.WordStages.word154_1_923
  rw [ssaStructural.eq_def]
  dsimp only
  rw [node310_eq, node311_eq]
  kernel_rfl
theorem node313_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_954 state2350 2989 state65 = (program27334,state2393,3113) := by
  kernel_rfl
theorem node314_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_955 state64 453 state65 = (program27335,state2393,3113) := by
  unfold InitECandidate.Proofs.WordStages.word154_1_955
  rw [ssaStructural.eq_def]
  dsimp only
  rw [node312_eq, node313_eq]
  kernel_rfl
theorem node315_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_959 state2393 3113 state65 = (program27344,state2419,3133) := by
  kernel_rfl
theorem node316_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_960 state64 453 state65 = (program27345,state2419,3133) := by
  unfold InitECandidate.Proofs.WordStages.word154_1_960
  rw [ssaStructural.eq_def]
  dsimp only
  rw [node314_eq, node315_eq]
  kernel_rfl
theorem node317_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_961 state2419 3133 state65 = (program27346,state2432,3137) := by
  kernel_rfl
theorem node318_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_962 state64 453 state65 = (program27347,state2432,3137) := by
  unfold InitECandidate.Proofs.WordStages.word154_1_962
  rw [ssaStructural.eq_def]
  dsimp only
  rw [node316_eq, node317_eq]
  kernel_rfl
theorem node319_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_991 state2432 3137 state65 = (program27407,state2473,3261) := by
  kernel_rfl
end InitECandidate.Proofs.SsaCheckpoints154
