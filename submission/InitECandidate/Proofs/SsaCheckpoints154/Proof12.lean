import InitECandidate.Proofs.CompactComputation
import InitECandidate.Proofs.SsaCheckpoints154.Proof11
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
open Flapjack Flapjack.Compiler.Backend
open InitECandidate.Proofs.SmallSsaKernelComputation
namespace InitECandidate.Proofs.SsaCheckpoints154
theorem node768_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_2092 state64 453 state65 = (program32989,state7816,14441) := by
  unfold InitECandidate.Proofs.WordStages.word154_1_2092
  rw [ssaStructural.eq_def]
  dsimp only
  rw [node760_eq, node767_eq]
  kernel_rfl
theorem node769_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_1557 state7816 14441 state65 = (program32990,state7828,14445) := by
  kernel_rfl
theorem node770_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_2093 state64 453 state65 = (program32991,state7828,14445) := by
  unfold InitECandidate.Proofs.WordStages.word154_1_2093
  rw [ssaStructural.eq_def]
  dsimp only
  rw [node768_eq, node769_eq]
  kernel_rfl
theorem node771_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_2096 state7828 14445 state65 = (program33052,state7870,14569) := by
  kernel_rfl
theorem node772_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_2097 state64 453 state65 = (program33053,state7870,14569) := by
  unfold InitECandidate.Proofs.WordStages.word154_1_2097
  rw [ssaStructural.eq_def]
  dsimp only
  rw [node770_eq, node771_eq]
  kernel_rfl
theorem node773_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_886 state7870 14569 state65 = (program33062,state7896,14589) := by
  kernel_rfl
theorem node774_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_2098 state64 453 state65 = (program33063,state7896,14589) := by
  unfold InitECandidate.Proofs.WordStages.word154_1_2098
  rw [ssaStructural.eq_def]
  dsimp only
  rw [node772_eq, node773_eq]
  kernel_rfl
theorem node775_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_888 state7896 14589 state65 = (program33064,state7909,14593) := by
  kernel_rfl
theorem node776_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_2099 state64 453 state65 = (program33065,state7909,14593) := by
  unfold InitECandidate.Proofs.WordStages.word154_1_2099
  rw [ssaStructural.eq_def]
  dsimp only
  rw [node774_eq, node775_eq]
  kernel_rfl
theorem node777_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_922 state7909 14593 state65 = (program33126,state7949,14717) := by
  kernel_rfl
theorem node778_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_2100 state64 453 state65 = (program33127,state7949,14717) := by
  unfold InitECandidate.Proofs.WordStages.word154_1_2100
  rw [ssaStructural.eq_def]
  dsimp only
  rw [node776_eq, node777_eq]
  kernel_rfl
theorem node779_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_1598 state7949 14717 state65 = (program33188,state7985,14841) := by
  kernel_rfl
theorem node780_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_1599 state7985 14841 state65 = (program33191,state8003,14849) := by
  kernel_rfl
theorem node781_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_1600 state7949 14717 state65 = (program33192,state8003,14849) := by
  unfold InitECandidate.Proofs.WordStages.word154_1_1600
  rw [ssaStructural.eq_def]
  dsimp only
  rw [node779_eq, node780_eq]
  kernel_rfl
theorem node782_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_590 state8003 14849 state65 = (program33193,state8011,14853) := by
  kernel_rfl
theorem node783_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_1601 state7949 14717 state65 = (program33194,state8011,14853) := by
  unfold InitECandidate.Proofs.WordStages.word154_1_1601
  rw [ssaStructural.eq_def]
  dsimp only
  rw [node781_eq, node782_eq]
  kernel_rfl
theorem node784_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_592 state8011 14853 state65 = (program33195,state8019,14857) := by
  kernel_rfl
theorem node785_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_1602 state7949 14717 state65 = (program33196,state8019,14857) := by
  unfold InitECandidate.Proofs.WordStages.word154_1_1602
  rw [ssaStructural.eq_def]
  dsimp only
  rw [node783_eq, node784_eq]
  kernel_rfl
theorem node786_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_2101 state64 453 state65 = (program33197,state8019,14857) := by
  unfold InitECandidate.Proofs.WordStages.word154_1_2101
  rw [ssaStructural.eq_def]
  dsimp only
  rw [node778_eq, node785_eq]
  kernel_rfl
theorem node787_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_1604 state8019 14857 state65 = (program33198,state8030,14861) := by
  kernel_rfl
theorem node788_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_2102 state64 453 state65 = (program33199,state8030,14861) := by
  unfold InitECandidate.Proofs.WordStages.word154_1_2102
  rw [ssaStructural.eq_def]
  dsimp only
  rw [node786_eq, node787_eq]
  kernel_rfl
theorem node789_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_2105 state8030 14861 state65 = (program33260,state8073,14985) := by
  kernel_rfl
theorem node790_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_2106 state64 453 state65 = (program33261,state8073,14985) := by
  unfold InitECandidate.Proofs.WordStages.word154_1_2106
  rw [ssaStructural.eq_def]
  dsimp only
  rw [node788_eq, node789_eq]
  kernel_rfl
theorem node791_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_959 state8073 14985 state65 = (program33270,state8099,15005) := by
  kernel_rfl
theorem node792_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_2107 state64 453 state65 = (program33271,state8099,15005) := by
  unfold InitECandidate.Proofs.WordStages.word154_1_2107
  rw [ssaStructural.eq_def]
  dsimp only
  rw [node790_eq, node791_eq]
  kernel_rfl
theorem node793_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_961 state8099 15005 state65 = (program33272,state8112,15009) := by
  kernel_rfl
theorem node794_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_2108 state64 453 state65 = (program33273,state8112,15009) := by
  unfold InitECandidate.Proofs.WordStages.word154_1_2108
  rw [ssaStructural.eq_def]
  dsimp only
  rw [node792_eq, node793_eq]
  kernel_rfl
theorem node795_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_991 state8112 15009 state65 = (program33334,state8153,15133) := by
  kernel_rfl
theorem node796_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_2109 state64 453 state65 = (program33335,state8153,15133) := by
  unfold InitECandidate.Proofs.WordStages.word154_1_2109
  rw [ssaStructural.eq_def]
  dsimp only
  rw [node794_eq, node795_eq]
  kernel_rfl
theorem node797_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_1645 state8153 15133 state65 = (program33396,state8187,15257) := by
  kernel_rfl
theorem node798_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_1646 state8187 15257 state65 = (program33399,state8207,15265) := by
  kernel_rfl
theorem node799_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_1647 state8153 15133 state65 = (program33400,state8207,15265) := by
  unfold InitECandidate.Proofs.WordStages.word154_1_1647
  rw [ssaStructural.eq_def]
  dsimp only
  rw [node797_eq, node798_eq]
  kernel_rfl
theorem node800_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_590 state8207 15265 state65 = (program33401,state8215,15269) := by
  kernel_rfl
theorem node801_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_1648 state8153 15133 state65 = (program33402,state8215,15269) := by
  unfold InitECandidate.Proofs.WordStages.word154_1_1648
  rw [ssaStructural.eq_def]
  dsimp only
  rw [node799_eq, node800_eq]
  kernel_rfl
theorem node802_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_592 state8215 15269 state65 = (program33403,state8223,15273) := by
  kernel_rfl
theorem node803_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_1649 state8153 15133 state65 = (program33404,state8223,15273) := by
  unfold InitECandidate.Proofs.WordStages.word154_1_1649
  rw [ssaStructural.eq_def]
  dsimp only
  rw [node801_eq, node802_eq]
  kernel_rfl
theorem node804_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_2110 state64 453 state65 = (program33405,state8223,15273) := by
  unfold InitECandidate.Proofs.WordStages.word154_1_2110
  rw [ssaStructural.eq_def]
  dsimp only
  rw [node796_eq, node803_eq]
  kernel_rfl
theorem node805_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_1651 state8223 15273 state65 = (program33406,state8236,15277) := by
  kernel_rfl
theorem node806_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_2111 state64 453 state65 = (program33407,state8236,15277) := by
  unfold InitECandidate.Proofs.WordStages.word154_1_2111
  rw [ssaStructural.eq_def]
  dsimp only
  rw [node804_eq, node805_eq]
  kernel_rfl
theorem node807_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_2114 state8236 15277 state65 = (program33468,state8281,15401) := by
  kernel_rfl
theorem node808_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_2115 state64 453 state65 = (program33469,state8281,15401) := by
  unfold InitECandidate.Proofs.WordStages.word154_1_2115
  rw [ssaStructural.eq_def]
  dsimp only
  rw [node806_eq, node807_eq]
  kernel_rfl
theorem node809_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_1028 state8281 15401 state65 = (program33478,state8305,15421) := by
  kernel_rfl
theorem node810_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_2116 state64 453 state65 = (program33479,state8305,15421) := by
  unfold InitECandidate.Proofs.WordStages.word154_1_2116
  rw [ssaStructural.eq_def]
  dsimp only
  rw [node808_eq, node809_eq]
  kernel_rfl
theorem node811_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_1030 state8305 15421 state65 = (program33480,state8316,15425) := by
  kernel_rfl
theorem node812_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_2117 state64 453 state65 = (program33481,state8316,15425) := by
  unfold InitECandidate.Proofs.WordStages.word154_1_2117
  rw [ssaStructural.eq_def]
  dsimp only
  rw [node810_eq, node811_eq]
  kernel_rfl
theorem node813_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_1059 state8316 15425 state65 = (program33542,state8357,15549) := by
  kernel_rfl
theorem node814_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_2118 state64 453 state65 = (program33543,state8357,15549) := by
  unfold InitECandidate.Proofs.WordStages.word154_1_2118
  rw [ssaStructural.eq_def]
  dsimp only
  rw [node812_eq, node813_eq]
  kernel_rfl
theorem node815_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_1691 state8357 15549 state65 = (program33604,state8389,15673) := by
  kernel_rfl
theorem node816_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_1692 state8389 15673 state65 = (program33607,state8409,15681) := by
  kernel_rfl
theorem node817_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_1693 state8357 15549 state65 = (program33608,state8409,15681) := by
  unfold InitECandidate.Proofs.WordStages.word154_1_1693
  rw [ssaStructural.eq_def]
  dsimp only
  rw [node815_eq, node816_eq]
  kernel_rfl
theorem node818_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_590 state8409 15681 state65 = (program33609,state8417,15685) := by
  kernel_rfl
theorem node819_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_1694 state8357 15549 state65 = (program33610,state8417,15685) := by
  unfold InitECandidate.Proofs.WordStages.word154_1_1694
  rw [ssaStructural.eq_def]
  dsimp only
  rw [node817_eq, node818_eq]
  kernel_rfl
theorem node820_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_592 state8417 15685 state65 = (program33611,state8425,15689) := by
  kernel_rfl
theorem node821_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_1695 state8357 15549 state65 = (program33612,state8425,15689) := by
  unfold InitECandidate.Proofs.WordStages.word154_1_1695
  rw [ssaStructural.eq_def]
  dsimp only
  rw [node819_eq, node820_eq]
  kernel_rfl
theorem node822_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_2119 state64 453 state65 = (program33613,state8425,15689) := by
  unfold InitECandidate.Proofs.WordStages.word154_1_2119
  rw [ssaStructural.eq_def]
  dsimp only
  rw [node814_eq, node821_eq]
  kernel_rfl
theorem node823_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_1697 state8425 15689 state65 = (program33614,state8438,15693) := by
  kernel_rfl
theorem node824_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_2120 state64 453 state65 = (program33615,state8438,15693) := by
  unfold InitECandidate.Proofs.WordStages.word154_1_2120
  rw [ssaStructural.eq_def]
  dsimp only
  rw [node822_eq, node823_eq]
  kernel_rfl
theorem node825_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_2123 state8438 15693 state65 = (program33676,state8482,15817) := by
  kernel_rfl
theorem node826_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_2124 state64 453 state65 = (program33677,state8482,15817) := by
  unfold InitECandidate.Proofs.WordStages.word154_1_2124
  rw [ssaStructural.eq_def]
  dsimp only
  rw [node824_eq, node825_eq]
  kernel_rfl
theorem node827_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_1094 state8482 15817 state65 = (program33686,state8504,15837) := by
  kernel_rfl
theorem node828_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_2125 state64 453 state65 = (program33687,state8504,15837) := by
  unfold InitECandidate.Proofs.WordStages.word154_1_2125
  rw [ssaStructural.eq_def]
  dsimp only
  rw [node826_eq, node827_eq]
  kernel_rfl
theorem node829_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_1096 state8504 15837 state65 = (program33688,state8514,15841) := by
  kernel_rfl
theorem node830_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_2126 state64 453 state65 = (program33689,state8514,15841) := by
  unfold InitECandidate.Proofs.WordStages.word154_1_2126
  rw [ssaStructural.eq_def]
  dsimp only
  rw [node828_eq, node829_eq]
  kernel_rfl
theorem node831_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_1125 state8514 15841 state65 = (program33750,state8556,15965) := by
  kernel_rfl
end InitECandidate.Proofs.SsaCheckpoints154
