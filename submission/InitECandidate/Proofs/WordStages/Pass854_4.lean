import InitECandidate.Proofs.CompactComputation
import InitECandidate.Proofs.WordStages.Pass854_3
import InitECandidate.Proofs.CompilerComputation
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open scoped InitECandidate.Proofs.CompilerComputation
open Flapjack Flapjack.Compiler.Backend Flapjack.Compiler.Encoders.RiscV.Target
namespace InitECandidate.Proofs.WordStages
def word854_4_1153 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.move 0 [(3529, 3489)]

def word854_4_1154 : WordLangProgHOL (BitVec 64) :=
.seq word854_2_1371 word854_4_1153

def word854_4_1155 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.move 1 [(3533, 3493)]

def word854_4_1156 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.move 0 [(3537, 3497)]

def word854_4_1157 : WordLangProgHOL (BitVec 64) :=
.seq word854_4_1155 word854_4_1156

def word854_4_1158 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.move 0 [(3541, 3501)]

def word854_4_1159 : WordLangProgHOL (BitVec 64) :=
.seq word854_4_1157 word854_4_1158

def word854_4_1161 : WordLangProgHOL (BitVec 64) :=
.seq word854_4_1159 word854_2_1379

def word854_4_1163 : WordLangProgHOL (BitVec 64) :=
.seq word854_4_1161 word854_2_1381

def word854_4_1164 : WordLangProgHOL (BitVec 64) :=
.seq word854_4_1154 word854_4_1163

def word854_4_1166 : WordLangProgHOL (BitVec 64) :=
.seq word854_4_1164 word854_2_1384

def word854_4_1167 : WordLangProgHOL (BitVec 64) :=
.seq word854_3_1151 word854_4_1166

def word854_4_1169 : WordLangProgHOL (BitVec 64) :=
.seq word854_4_1167 word854_2_1387

def word854_4_1171 : WordLangProgHOL (BitVec 64) :=
.seq word854_4_1169 word854_2_1389

def word854_4_1175 : WordLangProgHOL (BitVec 64) :=
.seq word854_4_1171 word854_2_1393

def word854_4_1179 : WordLangProgHOL (BitVec 64) :=
.seq word854_4_1175 word854_2_1397

def word854_4_1181 : WordLangProgHOL (BitVec 64) :=
.seq word854_4_1179 word854_2_1399

def word854_4_1185 : WordLangProgHOL (BitVec 64) :=
.seq word854_4_1181 word854_2_1403

def word854_4_1187 : WordLangProgHOL (BitVec 64) :=
.seq word854_4_1185 word854_3_1186

def word854_4_1194 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.less) 3257 (Flapjack.WordRegImm.reg 3261) word854_4_1187 word854_3_1193

def word854_4_1195 : WordLangProgHOL (BitVec 64) :=
.seq word854_2_1294 word854_4_1194

def word854_4_1196 : WordLangProgHOL (BitVec 64) :=
.seq word854_4_1195 word854_0_10

def word854_4_1198 : WordLangProgHOL (BitVec 64) :=
.seq word854_4_1196 word854_2_1438

def word854_4_1199 : WordLangProgHOL (BitVec 64) :=
.loop (Flapjack.Spt.bn Flapjack.Spt.ln
  (Flapjack.Spt.bn
    (Flapjack.Spt.bn
      (Flapjack.Spt.bn
        (Flapjack.Spt.bn
          (Flapjack.Spt.bn
            (Flapjack.Spt.bn
              (Flapjack.Spt.bn Flapjack.Spt.ln
                (Flapjack.Spt.bn Flapjack.Spt.ln
                  (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln))))
              Flapjack.Spt.ln)
            (Flapjack.Spt.bn Flapjack.Spt.ln
              (Flapjack.Spt.bn
                (Flapjack.Spt.bn Flapjack.Spt.ln
                  (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln)))
                Flapjack.Spt.ln)))
          (Flapjack.Spt.bn
            (Flapjack.Spt.bn
              (Flapjack.Spt.bn Flapjack.Spt.ln
                (Flapjack.Spt.bn Flapjack.Spt.ln
                  (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln))))
              (Flapjack.Spt.bn
                (Flapjack.Spt.bn Flapjack.Spt.ln
                  (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln)))
                Flapjack.Spt.ln))
            (Flapjack.Spt.bn Flapjack.Spt.ln
              (Flapjack.Spt.bn
                (Flapjack.Spt.bn Flapjack.Spt.ln
                  (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln)))
                Flapjack.Spt.ln))))
        (Flapjack.Spt.bn
          (Flapjack.Spt.bn
            (Flapjack.Spt.bn
              (Flapjack.Spt.bn Flapjack.Spt.ln
                (Flapjack.Spt.bn Flapjack.Spt.ln
                  (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln))))
              (Flapjack.Spt.bn
                (Flapjack.Spt.bn Flapjack.Spt.ln
                  (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln)))
                Flapjack.Spt.ln))
            (Flapjack.Spt.bn Flapjack.Spt.ln
              (Flapjack.Spt.bn
                (Flapjack.Spt.bn Flapjack.Spt.ln
                  (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln)))
                Flapjack.Spt.ln)))
          (Flapjack.Spt.bn
            (Flapjack.Spt.bn Flapjack.Spt.ln
              (Flapjack.Spt.bn
                (Flapjack.Spt.bn Flapjack.Spt.ln
                  (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln)))
                Flapjack.Spt.ln))
            (Flapjack.Spt.bn Flapjack.Spt.ln
              (Flapjack.Spt.bn
                (Flapjack.Spt.bn Flapjack.Spt.ln
                  (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln)))
                Flapjack.Spt.ln)))))
      (Flapjack.Spt.bn
        (Flapjack.Spt.bn
          (Flapjack.Spt.bn
            (Flapjack.Spt.bn
              (Flapjack.Spt.bn Flapjack.Spt.ln
                (Flapjack.Spt.bn Flapjack.Spt.ln
                  (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln))))
              Flapjack.Spt.ln)
            (Flapjack.Spt.bn Flapjack.Spt.ln
              (Flapjack.Spt.bn
                (Flapjack.Spt.bn Flapjack.Spt.ln
                  (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln)))
                Flapjack.Spt.ln)))
          (Flapjack.Spt.bn
            (Flapjack.Spt.bn Flapjack.Spt.ln
              (Flapjack.Spt.bn
                (Flapjack.Spt.bn Flapjack.Spt.ln
                  (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln)))
                Flapjack.Spt.ln))
            (Flapjack.Spt.bn Flapjack.Spt.ln
              (Flapjack.Spt.bn
                (Flapjack.Spt.bn Flapjack.Spt.ln
                  (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln)))
                Flapjack.Spt.ln))))
        (Flapjack.Spt.bn
          (Flapjack.Spt.bn
            (Flapjack.Spt.bn
              (Flapjack.Spt.bn Flapjack.Spt.ln
                (Flapjack.Spt.bn Flapjack.Spt.ln
                  (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln))))
              (Flapjack.Spt.bn
                (Flapjack.Spt.bn Flapjack.Spt.ln
                  (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln)))
                Flapjack.Spt.ln))
            (Flapjack.Spt.bn Flapjack.Spt.ln
              (Flapjack.Spt.bn
                (Flapjack.Spt.bn Flapjack.Spt.ln
                  (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln)))
                Flapjack.Spt.ln)))
          (Flapjack.Spt.bn
            (Flapjack.Spt.bn Flapjack.Spt.ln
              (Flapjack.Spt.bn
                (Flapjack.Spt.bn Flapjack.Spt.ln
                  (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln)))
                Flapjack.Spt.ln))
            (Flapjack.Spt.bn Flapjack.Spt.ln
              (Flapjack.Spt.bn
                (Flapjack.Spt.bn Flapjack.Spt.ln
                  (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln)))
                Flapjack.Spt.ln))))))
    Flapjack.Spt.ln)) word854_4_1198 (Flapjack.Spt.bn Flapjack.Spt.ln
  (Flapjack.Spt.bn
    (Flapjack.Spt.bn
      (Flapjack.Spt.bn
        (Flapjack.Spt.bn
          (Flapjack.Spt.bn Flapjack.Spt.ln
            (Flapjack.Spt.bn Flapjack.Spt.ln
              (Flapjack.Spt.bn
                (Flapjack.Spt.bn Flapjack.Spt.ln
                  (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln)))
                Flapjack.Spt.ln)))
          (Flapjack.Spt.bn
            (Flapjack.Spt.bn
              (Flapjack.Spt.bn Flapjack.Spt.ln
                (Flapjack.Spt.bn Flapjack.Spt.ln
                  (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln))))
              Flapjack.Spt.ln)
            Flapjack.Spt.ln))
        (Flapjack.Spt.bn
          (Flapjack.Spt.bn
            (Flapjack.Spt.bn
              (Flapjack.Spt.bn Flapjack.Spt.ln
                (Flapjack.Spt.bn Flapjack.Spt.ln
                  (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln))))
              Flapjack.Spt.ln)
            (Flapjack.Spt.bn Flapjack.Spt.ln
              (Flapjack.Spt.bn
                (Flapjack.Spt.bn Flapjack.Spt.ln
                  (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln)))
                Flapjack.Spt.ln)))
          (Flapjack.Spt.bn Flapjack.Spt.ln
            (Flapjack.Spt.bn Flapjack.Spt.ln
              (Flapjack.Spt.bn
                (Flapjack.Spt.bn Flapjack.Spt.ln
                  (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln)))
                Flapjack.Spt.ln)))))
      (Flapjack.Spt.bn
        (Flapjack.Spt.bn
          (Flapjack.Spt.bn Flapjack.Spt.ln
            (Flapjack.Spt.bn Flapjack.Spt.ln
              (Flapjack.Spt.bn
                (Flapjack.Spt.bn Flapjack.Spt.ln
                  (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln)))
                Flapjack.Spt.ln)))
          Flapjack.Spt.ln)
        (Flapjack.Spt.bn
          (Flapjack.Spt.bn
            (Flapjack.Spt.bn
              (Flapjack.Spt.bn Flapjack.Spt.ln
                (Flapjack.Spt.bn Flapjack.Spt.ln
                  (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln))))
              (Flapjack.Spt.bn
                (Flapjack.Spt.bn Flapjack.Spt.ln
                  (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln)))
                Flapjack.Spt.ln))
            Flapjack.Spt.ln)
          Flapjack.Spt.ln)))
    Flapjack.Spt.ln))

def word854_4_1200 : WordLangProgHOL (BitVec 64) :=
.seq word854_2_1290 word854_4_1199

def word854_4_1201 : WordLangProgHOL (BitVec 64) :=
.seq word854_3_1084 word854_4_1200

def word854_4_1202 : WordLangProgHOL (BitVec 64) :=
.seq word854_4_1201 word854_0_10

def word854_4_1210 : WordLangProgHOL (BitVec 64) :=
.seq word854_4_1202 word854_2_1450

def word854_4_1212 : WordLangProgHOL (BitVec 64) :=
.seq word854_4_1210 word854_2_1452

def word854_4_1214 : WordLangProgHOL (BitVec 64) :=
.seq word854_4_1212 word854_2_1454

def word854_4_1226 : WordLangProgHOL (BitVec 64) :=
.seq word854_4_1214 word854_3_1225

def word854_4_1227 : WordLangProgHOL (BitVec 64) :=
.seq word854_4_1226 word854_0_10

def word854_4_1231 : WordLangProgHOL (BitVec 64) :=
.seq word854_4_1227 word854_2_1486

def word854_4_1253 : WordLangProgHOL (BitVec 64) :=
.seq word854_4_1231 word854_3_1252

def word854_4_1254 : WordLangProgHOL (BitVec 64) :=
.seq word854_4_1253 word854_0_10

def word854_4_1256 : WordLangProgHOL (BitVec 64) :=
.seq word854_4_1254 word854_2_1520

def word854_4_1258 : WordLangProgHOL (BitVec 64) :=
.seq word854_4_1256 word854_2_1522

def word854_4_1260 : WordLangProgHOL (BitVec 64) :=
.seq word854_4_1258 word854_2_1524

def word854_4_1272 : WordLangProgHOL (BitVec 64) :=
.seq word854_4_1260 word854_3_1271

def word854_4_1273 : WordLangProgHOL (BitVec 64) :=
.seq word854_4_1272 word854_0_10

def word854_4_1277 : WordLangProgHOL (BitVec 64) :=
.seq word854_4_1273 word854_2_1556

def word854_4_1281 : WordLangProgHOL (BitVec 64) :=
.seq word854_4_1277 word854_2_1560

def word854_4_1283 : WordLangProgHOL (BitVec 64) :=
.seq word854_4_1281 word854_2_1562

def word854_4_1295 : WordLangProgHOL (BitVec 64) :=
.seq word854_4_1283 word854_3_1294

def word854_4_1296 : WordLangProgHOL (BitVec 64) :=
.seq word854_4_1295 word854_0_10

def word854_4_1298 : WordLangProgHOL (BitVec 64) :=
.seq word854_4_1296 word854_2_1592

def word854_4_1302 : WordLangProgHOL (BitVec 64) :=
.seq word854_4_1298 word854_2_1596

def word854_4_1303 : WordLangProgHOL (BitVec 64) :=
.seq word854_2_0 word854_4_1302

def pass854_4 : WordLangProgHOL (BitVec 64) :=
word854_4_1303
theorem pass854_4_eq : WordCse.wordCommonSubexpElim (pass854_3) = pass854_4 := by
  kernel_rfl
#print axioms pass854_4_eq
end InitECandidate.Proofs.WordStages
