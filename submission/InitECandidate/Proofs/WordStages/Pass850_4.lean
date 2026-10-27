import InitECandidate.Proofs.CompactComputation
import InitECandidate.Proofs.WordStages.Pass850_3
import InitECandidate.Proofs.CompilerComputation
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open scoped InitECandidate.Proofs.CompilerComputation
open Flapjack Flapjack.Compiler.Backend Flapjack.Compiler.Encoders.RiscV.Target
namespace InitECandidate.Proofs.WordStages
def word850_4_64 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.move 1 [(229, 209)]

def word850_4_65 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.move 0 [(233, 213)]

def word850_4_66 : WordLangProgHOL (BitVec 64) :=
.seq word850_4_64 word850_4_65

def word850_4_67 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.move 0 [(237, 217)]

def word850_4_68 : WordLangProgHOL (BitVec 64) :=
.seq word850_4_66 word850_4_67

def word850_4_69 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.move 0 [(241, 221)]

def word850_4_70 : WordLangProgHOL (BitVec 64) :=
.seq word850_4_68 word850_4_69

def word850_4_72 : WordLangProgHOL (BitVec 64) :=
.seq word850_4_70 word850_2_95

def word850_4_73 : WordLangProgHOL (BitVec 64) :=
.seq word850_3_63 word850_4_72

def word850_4_74 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.move 1 [(249, 229)]

def word850_4_75 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.move 0 [(253, 233)]

def word850_4_76 : WordLangProgHOL (BitVec 64) :=
.seq word850_4_74 word850_4_75

def word850_4_77 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.move 0 [(257, 237)]

def word850_4_78 : WordLangProgHOL (BitVec 64) :=
.seq word850_4_76 word850_4_77

def word850_4_80 : WordLangProgHOL (BitVec 64) :=
.seq word850_4_78 word850_2_103

def word850_4_82 : WordLangProgHOL (BitVec 64) :=
.seq word850_4_80 word850_2_105

def word850_4_83 : WordLangProgHOL (BitVec 64) :=
.seq word850_4_73 word850_4_82

def word850_4_87 : WordLangProgHOL (BitVec 64) :=
.seq word850_4_83 word850_2_110

def word850_4_89 : WordLangProgHOL (BitVec 64) :=
.seq word850_4_87 word850_2_112

def word850_4_90 : WordLangProgHOL (BitVec 64) :=
.seq word850_4_89 word850_0_5

def word850_4_721 : WordLangProgHOL (BitVec 64) :=
.seq word850_4_90 word850_3_720

def word850_4_722 : WordLangProgHOL (BitVec 64) :=
.seq word850_4_721 word850_0_5

def word850_4_724 : WordLangProgHOL (BitVec 64) :=
.seq word850_4_722 word850_2_1500

def word850_4_734 : WordLangProgHOL (BitVec 64) :=
.seq word850_4_724 word850_2_1510

def word850_4_754 : WordLangProgHOL (BitVec 64) :=
.seq word850_4_734 word850_3_753

def word850_4_755 : WordLangProgHOL (BitVec 64) :=
.seq word850_4_754 word850_0_5

def word850_4_757 : WordLangProgHOL (BitVec 64) :=
.seq word850_4_755 word850_2_1544

def word850_4_758 : WordLangProgHOL (BitVec 64) :=
.seq word850_4_757 word850_0_5

def word850_4_1048 : WordLangProgHOL (BitVec 64) :=
.seq word850_4_758 word850_3_1047

def word850_4_1049 : WordLangProgHOL (BitVec 64) :=
.seq word850_4_1048 word850_0_5

def word850_4_1053 : WordLangProgHOL (BitVec 64) :=
.seq word850_4_1049 word850_2_2115

def word850_4_1055 : WordLangProgHOL (BitVec 64) :=
.seq word850_4_1053 word850_2_2117

def word850_4_1056 : WordLangProgHOL (BitVec 64) :=
.seq word850_4_1055 word850_0_5

def word850_4_1315 : WordLangProgHOL (BitVec 64) :=
.seq word850_4_1056 word850_3_1314

def word850_4_1316 : WordLangProgHOL (BitVec 64) :=
.seq word850_4_1315 word850_0_5

def word850_4_1318 : WordLangProgHOL (BitVec 64) :=
.seq word850_4_1316 word850_2_2633

def word850_4_1320 : WordLangProgHOL (BitVec 64) :=
.seq word850_4_1318 word850_2_2635

def word850_4_1332 : WordLangProgHOL (BitVec 64) :=
.seq word850_4_1320 word850_3_1331

def word850_4_1333 : WordLangProgHOL (BitVec 64) :=
.seq word850_4_1332 word850_0_5

def word850_4_1335 : WordLangProgHOL (BitVec 64) :=
.seq word850_4_1333 word850_2_2665

def word850_4_1339 : WordLangProgHOL (BitVec 64) :=
.seq word850_4_1335 word850_2_2669

def word850_4_1340 : WordLangProgHOL (BitVec 64) :=
.seq word850_2_0 word850_4_1339

def pass850_4 : WordLangProgHOL (BitVec 64) :=
word850_4_1340
theorem pass850_4_eq : WordCse.wordCommonSubexpElim (pass850_3) = pass850_4 := by
  kernel_rfl
#print axioms pass850_4_eq
end InitECandidate.Proofs.WordStages
