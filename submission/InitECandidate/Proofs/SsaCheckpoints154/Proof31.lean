import InitECandidate.Proofs.CompactComputation
import InitECandidate.Proofs.SsaCheckpoints154.Proof30
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
open Flapjack Flapjack.Compiler.Backend
open InitECandidate.Proofs.SmallSsaKernelComputation
namespace InitECandidate.Proofs.SsaCheckpoints154
theorem node1984_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_3061 state64 453 state65 = (program47158,state22385,43577) := by
  unfold InitECandidate.Proofs.WordStages.word154_1_3061
  rw [ssaStructural.eq_def]
  dsimp only
  rw [node1982_eq, node1983_eq]
  kernel_rfl
theorem node1985_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_0_1141 state22385 43577 state65 = (program47159,state22385,43577) := by
  kernel_rfl
theorem node1986_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_3062 state64 453 state65 = (program47160,state22385,43577) := by
  unfold InitECandidate.Proofs.WordStages.word154_1_3062
  rw [ssaStructural.eq_def]
  dsimp only
  rw [node1984_eq, node1985_eq]
  kernel_rfl
theorem node1987_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_3064 state22385 43577 state65 = (program47163,state22400,43585) := by
  kernel_rfl
theorem node1988_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_3065 state64 453 state65 = (program47164,state22400,43585) := by
  unfold InitECandidate.Proofs.WordStages.word154_1_3065
  rw [ssaStructural.eq_def]
  dsimp only
  rw [node1986_eq, node1987_eq]
  kernel_rfl
theorem node1989_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_3066 state22400 43585 state65 = (program47167,state22416,43593) := by
  kernel_rfl
theorem node1990_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_3067 state64 453 state65 = (program47168,state22416,43593) := by
  unfold InitECandidate.Proofs.WordStages.word154_1_3067
  rw [ssaStructural.eq_def]
  dsimp only
  rw [node1988_eq, node1989_eq]
  kernel_rfl
theorem node1991_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_0_1141 state22416 43593 state65 = (program47169,state22416,43593) := by
  kernel_rfl
theorem node1992_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_3068 state64 453 state65 = (program47170,state22416,43593) := by
  unfold InitECandidate.Proofs.WordStages.word154_1_3068
  rw [ssaStructural.eq_def]
  dsimp only
  rw [node1990_eq, node1991_eq]
  kernel_rfl
theorem node1993_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_3070 state22416 43593 state65 = (program47173,state22431,43601) := by
  kernel_rfl
theorem node1994_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_3071 state64 453 state65 = (program47174,state22431,43601) := by
  unfold InitECandidate.Proofs.WordStages.word154_1_3071
  rw [ssaStructural.eq_def]
  dsimp only
  rw [node1992_eq, node1993_eq]
  kernel_rfl
theorem node1995_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_3072 state22431 43601 state65 = (program47177,state22447,43609) := by
  kernel_rfl
theorem node1996_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_3073 state64 453 state65 = (program47178,state22447,43609) := by
  unfold InitECandidate.Proofs.WordStages.word154_1_3073
  rw [ssaStructural.eq_def]
  dsimp only
  rw [node1994_eq, node1995_eq]
  kernel_rfl
theorem node1997_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_0_1141 state22447 43609 state65 = (program47179,state22447,43609) := by
  kernel_rfl
theorem node1998_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_3074 state64 453 state65 = (program47180,state22447,43609) := by
  unfold InitECandidate.Proofs.WordStages.word154_1_3074
  rw [ssaStructural.eq_def]
  dsimp only
  rw [node1996_eq, node1997_eq]
  kernel_rfl
theorem node1999_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_3076 state22447 43609 state65 = (program47183,state22462,43617) := by
  kernel_rfl
theorem node2000_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_3077 state64 453 state65 = (program47184,state22462,43617) := by
  unfold InitECandidate.Proofs.WordStages.word154_1_3077
  rw [ssaStructural.eq_def]
  dsimp only
  rw [node1998_eq, node1999_eq]
  kernel_rfl
theorem node2001_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_3078 state22462 43617 state65 = (program47185,state22471,43621) := by
  kernel_rfl
theorem node2002_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_3079 state64 453 state65 = (program47186,state22471,43621) := by
  unfold InitECandidate.Proofs.WordStages.word154_1_3079
  rw [ssaStructural.eq_def]
  dsimp only
  rw [node2000_eq, node2001_eq]
  kernel_rfl
theorem node2003_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_0_1141 state22471 43621 state65 = (program47187,state22471,43621) := by
  kernel_rfl
theorem node2004_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_3080 state64 453 state65 = (program47188,state22471,43621) := by
  unfold InitECandidate.Proofs.WordStages.word154_1_3080
  rw [ssaStructural.eq_def]
  dsimp only
  rw [node2002_eq, node2003_eq]
  kernel_rfl
theorem node2005_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_3083 state22471 43621 state65 = (program47197,state22499,43641) := by
  kernel_rfl
theorem node2006_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_3084 state64 453 state65 = (program47198,state22499,43641) := by
  unfold InitECandidate.Proofs.WordStages.word154_1_3084
  rw [ssaStructural.eq_def]
  dsimp only
  rw [node2004_eq, node2005_eq]
  kernel_rfl
theorem node2007_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_1697 state22499 43641 state65 = (program47199,state22512,43645) := by
  kernel_rfl
theorem node2008_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_3085 state64 453 state65 = (program47200,state22512,43645) := by
  unfold InitECandidate.Proofs.WordStages.word154_1_3085
  rw [ssaStructural.eq_def]
  dsimp only
  rw [node2006_eq, node2007_eq]
  kernel_rfl
theorem node2009_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_3087 state22512 43645 state65 = (program47203,state22527,43653) := by
  kernel_rfl
theorem node2010_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_3088 state64 453 state65 = (program47204,state22527,43653) := by
  unfold InitECandidate.Proofs.WordStages.word154_1_3088
  rw [ssaStructural.eq_def]
  dsimp only
  rw [node2008_eq, node2009_eq]
  kernel_rfl
theorem node2011_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_3089 state22527 43653 state65 = (program47207,state22541,43661) := by
  kernel_rfl
theorem node2012_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_3090 state64 453 state65 = (program47208,state22541,43661) := by
  unfold InitECandidate.Proofs.WordStages.word154_1_3090
  rw [ssaStructural.eq_def]
  dsimp only
  rw [node2010_eq, node2011_eq]
  kernel_rfl
theorem node2013_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_0_1141 state22541 43661 state65 = (program47209,state22541,43661) := by
  kernel_rfl
theorem node2014_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_3091 state64 453 state65 = (program47210,state22541,43661) := by
  unfold InitECandidate.Proofs.WordStages.word154_1_3091
  rw [ssaStructural.eq_def]
  dsimp only
  rw [node2012_eq, node2013_eq]
  kernel_rfl
theorem node2015_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_3093 state22541 43661 state65 = (program47213,state22556,43669) := by
  kernel_rfl
theorem node2016_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_3094 state64 453 state65 = (program47214,state22556,43669) := by
  unfold InitECandidate.Proofs.WordStages.word154_1_3094
  rw [ssaStructural.eq_def]
  dsimp only
  rw [node2014_eq, node2015_eq]
  kernel_rfl
theorem node2017_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_3095 state22556 43669 state65 = (program47217,state22570,43677) := by
  kernel_rfl
theorem node2018_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_3096 state64 453 state65 = (program47218,state22570,43677) := by
  unfold InitECandidate.Proofs.WordStages.word154_1_3096
  rw [ssaStructural.eq_def]
  dsimp only
  rw [node2016_eq, node2017_eq]
  kernel_rfl
theorem node2019_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_0_1141 state22570 43677 state65 = (program47219,state22570,43677) := by
  kernel_rfl
theorem node2020_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_3097 state64 453 state65 = (program47220,state22570,43677) := by
  unfold InitECandidate.Proofs.WordStages.word154_1_3097
  rw [ssaStructural.eq_def]
  dsimp only
  rw [node2018_eq, node2019_eq]
  kernel_rfl
theorem node2021_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_3099 state22570 43677 state65 = (program47223,state22585,43685) := by
  kernel_rfl
theorem node2022_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_3100 state64 453 state65 = (program47224,state22585,43685) := by
  unfold InitECandidate.Proofs.WordStages.word154_1_3100
  rw [ssaStructural.eq_def]
  dsimp only
  rw [node2020_eq, node2021_eq]
  kernel_rfl
theorem node2023_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_3101 state22585 43685 state65 = (program47227,state22599,43693) := by
  kernel_rfl
theorem node2024_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_3102 state64 453 state65 = (program47228,state22599,43693) := by
  unfold InitECandidate.Proofs.WordStages.word154_1_3102
  rw [ssaStructural.eq_def]
  dsimp only
  rw [node2022_eq, node2023_eq]
  kernel_rfl
theorem node2025_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_0_1141 state22599 43693 state65 = (program47229,state22599,43693) := by
  kernel_rfl
theorem node2026_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_3103 state64 453 state65 = (program47230,state22599,43693) := by
  unfold InitECandidate.Proofs.WordStages.word154_1_3103
  rw [ssaStructural.eq_def]
  dsimp only
  rw [node2024_eq, node2025_eq]
  kernel_rfl
theorem node2027_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_3105 state22599 43693 state65 = (program47233,state22614,43701) := by
  kernel_rfl
theorem node2028_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_3106 state64 453 state65 = (program47234,state22614,43701) := by
  unfold InitECandidate.Proofs.WordStages.word154_1_3106
  rw [ssaStructural.eq_def]
  dsimp only
  rw [node2026_eq, node2027_eq]
  kernel_rfl
theorem node2029_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_3107 state22614 43701 state65 = (program47235,state22622,43705) := by
  kernel_rfl
theorem node2030_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_3108 state64 453 state65 = (program47236,state22622,43705) := by
  unfold InitECandidate.Proofs.WordStages.word154_1_3108
  rw [ssaStructural.eq_def]
  dsimp only
  rw [node2028_eq, node2029_eq]
  kernel_rfl
theorem node2031_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_0_1141 state22622 43705 state65 = (program47237,state22622,43705) := by
  kernel_rfl
theorem node2032_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_3109 state64 453 state65 = (program47238,state22622,43705) := by
  unfold InitECandidate.Proofs.WordStages.word154_1_3109
  rw [ssaStructural.eq_def]
  dsimp only
  rw [node2030_eq, node2031_eq]
  kernel_rfl
theorem node2033_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_3110 state22622 43705 state65 = (program47239,state22630,43709) := by
  kernel_rfl
theorem node2034_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_3111 state64 453 state65 = (program47240,state22630,43709) := by
  unfold InitECandidate.Proofs.WordStages.word154_1_3111
  rw [ssaStructural.eq_def]
  dsimp only
  rw [node2032_eq, node2033_eq]
  kernel_rfl
theorem node2035_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_0_1321 state22630 43709 state65 = (program47242,state22630,43709) := by
  kernel_rfl
theorem node2036_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_3113 state64 453 state65 = (program47243,state22630,43709) := by
  unfold InitECandidate.Proofs.WordStages.word154_1_3113
  rw [ssaStructural.eq_def]
  dsimp only
  rw [node2034_eq, node2035_eq]
  kernel_rfl
end InitECandidate.Proofs.SsaCheckpoints154
