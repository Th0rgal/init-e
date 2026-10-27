import InitECandidate.Proofs.CompactComputation
import InitECandidate.Proofs.WordStages.Pass617_3
import InitECandidate.Proofs.CompilerComputation
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open scoped InitECandidate.Proofs.CompilerComputation
open Flapjack Flapjack.Compiler.Backend Flapjack.Compiler.Encoders.RiscV.Target
namespace InitECandidate.Proofs.WordStages
def word617_4_753 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.move 1 [(6277, 6257)]

def word617_4_754 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.move 0 [(6281, 6261)]

def word617_4_755 : WordLangProgHOL (BitVec 64) :=
.seq word617_4_753 word617_4_754

def word617_4_756 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.move 0 [(6285, 6265)]

def word617_4_757 : WordLangProgHOL (BitVec 64) :=
.seq word617_4_755 word617_4_756

def word617_4_758 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.move 0 [(6289, 6269)]

def word617_4_759 : WordLangProgHOL (BitVec 64) :=
.seq word617_4_757 word617_4_758

def word617_4_761 : WordLangProgHOL (BitVec 64) :=
.seq word617_4_759 word617_2_1172

def word617_4_765 : WordLangProgHOL (BitVec 64) :=
.seq word617_4_761 word617_2_1176

def word617_4_766 : WordLangProgHOL (BitVec 64) :=
.seq word617_3_752 word617_4_765

def word617_4_768 : WordLangProgHOL (BitVec 64) :=
.seq word617_4_766 word617_2_1179

def word617_4_772 : WordLangProgHOL (BitVec 64) :=
.seq word617_4_768 word617_2_1183

def word617_4_774 : WordLangProgHOL (BitVec 64) :=
.seq word617_4_772 word617_2_1185

def word617_4_786 : WordLangProgHOL (BitVec 64) :=
.seq word617_4_774 word617_3_785

def word617_4_787 : WordLangProgHOL (BitVec 64) :=
.seq word617_4_786 word617_0_3

def word617_4_797 : WordLangProgHOL (BitVec 64) :=
.seq word617_4_787 word617_2_1223

def word617_4_798 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.move 1 [(6589, 6569)]

def word617_4_799 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.move 0 [(6593, 6573)]

def word617_4_800 : WordLangProgHOL (BitVec 64) :=
.seq word617_4_798 word617_4_799

def word617_4_801 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.move 0 [(6597, 6577)]

def word617_4_802 : WordLangProgHOL (BitVec 64) :=
.seq word617_4_800 word617_4_801

def word617_4_803 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.move 0 [(6601, 6581)]

def word617_4_804 : WordLangProgHOL (BitVec 64) :=
.seq word617_4_802 word617_4_803

def word617_4_806 : WordLangProgHOL (BitVec 64) :=
.seq word617_4_804 word617_2_1232

def word617_4_807 : WordLangProgHOL (BitVec 64) :=
.seq word617_4_797 word617_4_806

def word617_4_809 : WordLangProgHOL (BitVec 64) :=
.seq word617_4_807 word617_2_1237

def word617_4_813 : WordLangProgHOL (BitVec 64) :=
.seq word617_4_809 word617_2_1241

def word617_4_817 : WordLangProgHOL (BitVec 64) :=
.seq word617_4_813 word617_2_1245

def word617_4_835 : WordLangProgHOL (BitVec 64) :=
.seq word617_4_817 word617_3_834

def word617_4_836 : WordLangProgHOL (BitVec 64) :=
.seq word617_4_835 word617_0_3

def word617_4_840 : WordLangProgHOL (BitVec 64) :=
.seq word617_4_836 word617_2_1277

def word617_4_844 : WordLangProgHOL (BitVec 64) :=
.seq word617_4_840 word617_2_1281

def word617_4_848 : WordLangProgHOL (BitVec 64) :=
.seq word617_4_844 word617_2_1285

def word617_4_852 : WordLangProgHOL (BitVec 64) :=
.seq word617_4_848 word617_2_1289

def word617_4_854 : WordLangProgHOL (BitVec 64) :=
.seq word617_4_852 word617_2_1291

def word617_4_856 : WordLangProgHOL (BitVec 64) :=
.seq word617_4_854 word617_2_1293

def word617_4_858 : WordLangProgHOL (BitVec 64) :=
.seq word617_4_856 word617_2_1295

def word617_4_860 : WordLangProgHOL (BitVec 64) :=
.seq word617_4_858 word617_2_1297

def word617_4_878 : WordLangProgHOL (BitVec 64) :=
.seq word617_4_860 word617_3_877

def word617_4_879 : WordLangProgHOL (BitVec 64) :=
.seq word617_4_878 word617_0_3

def word617_4_881 : WordLangProgHOL (BitVec 64) :=
.seq word617_4_879 word617_2_1327

def word617_4_883 : WordLangProgHOL (BitVec 64) :=
.seq word617_4_881 word617_2_1329

def word617_4_885 : WordLangProgHOL (BitVec 64) :=
.seq word617_4_883 word617_2_1331

def word617_4_943 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.move 1 [(7441, 7417)]

def word617_4_944 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.move 0 [(7445, 7421)]

def word617_4_945 : WordLangProgHOL (BitVec 64) :=
.seq word617_4_943 word617_4_944

def word617_4_946 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.move 0 [(7449, 7425)]

def word617_4_947 : WordLangProgHOL (BitVec 64) :=
.seq word617_4_945 word617_4_946

def word617_4_948 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.move 0 [(7453, 7429)]

def word617_4_949 : WordLangProgHOL (BitVec 64) :=
.seq word617_4_947 word617_4_948

def word617_4_951 : WordLangProgHOL (BitVec 64) :=
.seq word617_4_949 word617_2_1451

def word617_4_953 : WordLangProgHOL (BitVec 64) :=
.seq word617_4_951 word617_2_1453

def word617_4_954 : WordLangProgHOL (BitVec 64) :=
.seq word617_2_1443 word617_4_953

def word617_4_955 : WordLangProgHOL (BitVec 64) :=
.seq word617_3_941 word617_4_954

def word617_4_957 : WordLangProgHOL (BitVec 64) :=
.seq word617_4_955 word617_2_1457

def word617_4_961 : WordLangProgHOL (BitVec 64) :=
.seq word617_4_957 word617_2_1461

def word617_4_962 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.move 1 [(7473, 7441)]

def word617_4_963 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.move 0 [(7477, 7445)]

def word617_4_964 : WordLangProgHOL (BitVec 64) :=
.seq word617_4_962 word617_4_963

def word617_4_965 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.move 0 [(7481, 7449)]

def word617_4_966 : WordLangProgHOL (BitVec 64) :=
.seq word617_4_964 word617_4_965

def word617_4_968 : WordLangProgHOL (BitVec 64) :=
.seq word617_4_966 word617_2_1468

def word617_4_970 : WordLangProgHOL (BitVec 64) :=
.seq word617_4_968 word617_2_1470

def word617_4_971 : WordLangProgHOL (BitVec 64) :=
.seq word617_4_961 word617_4_970

def word617_4_973 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.move 1 [(7497, 7473)]

def word617_4_974 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.move 0 [(7501, 7477)]

def word617_4_975 : WordLangProgHOL (BitVec 64) :=
.seq word617_4_973 word617_4_974

def word617_4_976 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.move 0 [(7505, 7481)]

def word617_4_977 : WordLangProgHOL (BitVec 64) :=
.seq word617_4_975 word617_4_976

def word617_4_978 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.move 0 [(7509, 7485)]

def word617_4_979 : WordLangProgHOL (BitVec 64) :=
.seq word617_4_977 word617_4_978

def word617_4_981 : WordLangProgHOL (BitVec 64) :=
.seq word617_4_979 word617_2_1481

def word617_4_983 : WordLangProgHOL (BitVec 64) :=
.seq word617_4_981 word617_2_1483

def word617_4_984 : WordLangProgHOL (BitVec 64) :=
.seq word617_2_1473 word617_4_983

def word617_4_985 : WordLangProgHOL (BitVec 64) :=
.seq word617_4_971 word617_4_984

def word617_4_987 : WordLangProgHOL (BitVec 64) :=
.seq word617_4_985 word617_2_1487

def word617_4_991 : WordLangProgHOL (BitVec 64) :=
.seq word617_4_987 word617_2_1491

def word617_4_993 : WordLangProgHOL (BitVec 64) :=
.seq word617_4_991 word617_2_1493

def word617_4_995 : WordLangProgHOL (BitVec 64) :=
.seq word617_4_993 word617_2_1495

def word617_4_1016 : WordLangProgHOL (BitVec 64) :=
.seq word617_4_995 word617_3_1015

def word617_4_1017 : WordLangProgHOL (BitVec 64) :=
.seq word617_4_1016 word617_0_3

def word617_4_1019 : WordLangProgHOL (BitVec 64) :=
.seq word617_4_1017 word617_3_1018

def word617_4_1189 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notEqual) 7201 (Flapjack.WordRegImm.reg 7205) word617_4_1019 word617_3_1188

def word617_4_1190 : WordLangProgHOL (BitVec 64) :=
.seq word617_4_885 word617_4_1189

def word617_4_1191 : WordLangProgHOL (BitVec 64) :=
.seq word617_4_1190 word617_0_3

def word617_4_1193 : WordLangProgHOL (BitVec 64) :=
.seq word617_4_1191 word617_2_1843

def word617_4_1195 : WordLangProgHOL (BitVec 64) :=
.seq word617_4_1193 word617_2_1845

def word617_4_1216 : WordLangProgHOL (BitVec 64) :=
.seq word617_4_1195 word617_3_1215

def word617_4_1217 : WordLangProgHOL (BitVec 64) :=
.seq word617_4_1216 word617_0_3

def word617_4_1219 : WordLangProgHOL (BitVec 64) :=
.seq word617_4_1217 word617_2_1938

def word617_4_1223 : WordLangProgHOL (BitVec 64) :=
.seq word617_4_1219 word617_2_1942

def word617_4_1224 : WordLangProgHOL (BitVec 64) :=
.seq word617_2_0 word617_4_1223

def pass617_4 : WordLangProgHOL (BitVec 64) :=
word617_4_1224
theorem pass617_4_eq : WordCse.wordCommonSubexpElim (pass617_3) = pass617_4 := by
  kernel_rfl
#print axioms pass617_4_eq
end InitECandidate.Proofs.WordStages
