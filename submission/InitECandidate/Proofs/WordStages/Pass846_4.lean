import InitECandidate.Proofs.CompactComputation
import InitECandidate.Proofs.WordStages.Pass846_3
import InitECandidate.Proofs.CompilerComputation
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open scoped InitECandidate.Proofs.CompilerComputation
open Flapjack Flapjack.Compiler.Backend Flapjack.Compiler.Encoders.RiscV.Target
namespace InitECandidate.Proofs.WordStages
def word846_4_64 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.move 1 [(229, 209)]

def word846_4_65 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.move 0 [(233, 213)]

def word846_4_66 : WordLangProgHOL (BitVec 64) :=
.seq word846_4_64 word846_4_65

def word846_4_67 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.move 0 [(237, 217)]

def word846_4_68 : WordLangProgHOL (BitVec 64) :=
.seq word846_4_66 word846_4_67

def word846_4_69 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.move 0 [(241, 221)]

def word846_4_70 : WordLangProgHOL (BitVec 64) :=
.seq word846_4_68 word846_4_69

def word846_4_72 : WordLangProgHOL (BitVec 64) :=
.seq word846_4_70 word846_2_95

def word846_4_73 : WordLangProgHOL (BitVec 64) :=
.seq word846_3_63 word846_4_72

def word846_4_74 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.move 1 [(249, 229)]

def word846_4_75 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.move 0 [(253, 233)]

def word846_4_76 : WordLangProgHOL (BitVec 64) :=
.seq word846_4_74 word846_4_75

def word846_4_77 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.move 0 [(257, 237)]

def word846_4_78 : WordLangProgHOL (BitVec 64) :=
.seq word846_4_76 word846_4_77

def word846_4_80 : WordLangProgHOL (BitVec 64) :=
.seq word846_4_78 word846_2_103

def word846_4_82 : WordLangProgHOL (BitVec 64) :=
.seq word846_4_80 word846_2_105

def word846_4_83 : WordLangProgHOL (BitVec 64) :=
.seq word846_4_73 word846_4_82

def word846_4_87 : WordLangProgHOL (BitVec 64) :=
.seq word846_4_83 word846_2_110

def word846_4_89 : WordLangProgHOL (BitVec 64) :=
.seq word846_4_87 word846_2_112

def word846_4_90 : WordLangProgHOL (BitVec 64) :=
.seq word846_4_89 word846_0_5

def word846_4_721 : WordLangProgHOL (BitVec 64) :=
.seq word846_4_90 word846_3_720

def word846_4_722 : WordLangProgHOL (BitVec 64) :=
.seq word846_4_721 word846_0_5

def word846_4_724 : WordLangProgHOL (BitVec 64) :=
.seq word846_4_722 word846_2_1500

def word846_4_734 : WordLangProgHOL (BitVec 64) :=
.seq word846_4_724 word846_2_1510

def word846_4_754 : WordLangProgHOL (BitVec 64) :=
.seq word846_4_734 word846_3_753

def word846_4_755 : WordLangProgHOL (BitVec 64) :=
.seq word846_4_754 word846_0_5

def word846_4_757 : WordLangProgHOL (BitVec 64) :=
.seq word846_4_755 word846_2_1544

def word846_4_758 : WordLangProgHOL (BitVec 64) :=
.seq word846_4_757 word846_0_5

def word846_4_1048 : WordLangProgHOL (BitVec 64) :=
.seq word846_4_758 word846_3_1047

def word846_4_1049 : WordLangProgHOL (BitVec 64) :=
.seq word846_4_1048 word846_0_5

def word846_4_1053 : WordLangProgHOL (BitVec 64) :=
.seq word846_4_1049 word846_2_2115

def word846_4_1055 : WordLangProgHOL (BitVec 64) :=
.seq word846_4_1053 word846_2_2117

def word846_4_1056 : WordLangProgHOL (BitVec 64) :=
.seq word846_4_1055 word846_0_5

def word846_4_1315 : WordLangProgHOL (BitVec 64) :=
.seq word846_4_1056 word846_3_1314

def word846_4_1316 : WordLangProgHOL (BitVec 64) :=
.seq word846_4_1315 word846_0_5

def word846_4_1318 : WordLangProgHOL (BitVec 64) :=
.seq word846_4_1316 word846_2_2633

def word846_4_1320 : WordLangProgHOL (BitVec 64) :=
.seq word846_4_1318 word846_2_2635

def word846_4_1332 : WordLangProgHOL (BitVec 64) :=
.seq word846_4_1320 word846_3_1331

def word846_4_1333 : WordLangProgHOL (BitVec 64) :=
.seq word846_4_1332 word846_0_5

def word846_4_1335 : WordLangProgHOL (BitVec 64) :=
.seq word846_4_1333 word846_2_2665

def word846_4_1339 : WordLangProgHOL (BitVec 64) :=
.seq word846_4_1335 word846_2_2669

def word846_4_1340 : WordLangProgHOL (BitVec 64) :=
.seq word846_2_0 word846_4_1339

def pass846_4 : WordLangProgHOL (BitVec 64) :=
word846_4_1340
theorem pass846_4_eq : WordCse.wordCommonSubexpElim (pass846_3) = pass846_4 := by
  kernel_rfl
#print axioms pass846_4_eq
end InitECandidate.Proofs.WordStages
