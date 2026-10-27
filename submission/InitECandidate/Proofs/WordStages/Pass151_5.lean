import InitECandidate.Proofs.CompactComputation
import InitECandidate.Proofs.WordStages.Pass151_4
import InitECandidate.Proofs.CompilerComputation
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open scoped InitECandidate.Proofs.CompilerComputation
open Flapjack Flapjack.Compiler.Backend Flapjack.Compiler.Encoders.RiscV.Target
namespace InitECandidate.Proofs.WordStages
def word151_5_12910 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.move 0 [(26029, 26005)]

def word151_5_12912 : WordLangProgHOL (BitVec 64) :=
.seq word151_5_12910 word151_2_12911

def word151_5_12913 : WordLangProgHOL (BitVec 64) :=
.seq word151_4_12909 word151_5_12912

def word151_5_12914 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.move 0 [(26033, 26029)]

def word151_5_12916 : WordLangProgHOL (BitVec 64) :=
.seq word151_5_12914 word151_2_12915

def word151_5_12917 : WordLangProgHOL (BitVec 64) :=
.seq word151_5_12913 word151_5_12916

def word151_5_12929 : WordLangProgHOL (BitVec 64) :=
.seq word151_5_12917 word151_2_12928

def word151_5_12931 : WordLangProgHOL (BitVec 64) :=
.seq word151_5_12929 word151_2_12930

def word151_5_12935 : WordLangProgHOL (BitVec 64) :=
.seq word151_5_12931 word151_2_12934

def word151_5_12939 : WordLangProgHOL (BitVec 64) :=
.seq word151_5_12935 word151_2_12938

def word151_5_12951 : WordLangProgHOL (BitVec 64) :=
.seq word151_5_12939 word151_2_12950

def word151_5_12953 : WordLangProgHOL (BitVec 64) :=
.seq word151_5_12951 word151_2_12952

def word151_5_12957 : WordLangProgHOL (BitVec 64) :=
.seq word151_5_12953 word151_2_12956

def word151_5_12961 : WordLangProgHOL (BitVec 64) :=
.seq word151_5_12957 word151_2_12960

def word151_5_12973 : WordLangProgHOL (BitVec 64) :=
.seq word151_5_12961 word151_2_12972

def word151_5_12975 : WordLangProgHOL (BitVec 64) :=
.seq word151_5_12973 word151_2_12974

def word151_5_12979 : WordLangProgHOL (BitVec 64) :=
.seq word151_5_12975 word151_2_12978

def word151_5_12983 : WordLangProgHOL (BitVec 64) :=
.seq word151_5_12979 word151_2_12982

def word151_5_12995 : WordLangProgHOL (BitVec 64) :=
.seq word151_5_12983 word151_2_12994

def word151_5_12997 : WordLangProgHOL (BitVec 64) :=
.seq word151_5_12995 word151_2_12996

def word151_5_13001 : WordLangProgHOL (BitVec 64) :=
.seq word151_5_12997 word151_2_13000

def word151_5_13005 : WordLangProgHOL (BitVec 64) :=
.seq word151_5_13001 word151_2_13004

def word151_5_13017 : WordLangProgHOL (BitVec 64) :=
.seq word151_5_13005 word151_2_13016

def word151_5_13019 : WordLangProgHOL (BitVec 64) :=
.seq word151_5_13017 word151_2_13018

def word151_5_13023 : WordLangProgHOL (BitVec 64) :=
.seq word151_5_13019 word151_2_13022

def word151_5_13027 : WordLangProgHOL (BitVec 64) :=
.seq word151_5_13023 word151_2_13026

def word151_5_13039 : WordLangProgHOL (BitVec 64) :=
.seq word151_5_13027 word151_2_13038

def word151_5_13041 : WordLangProgHOL (BitVec 64) :=
.seq word151_5_13039 word151_2_13040

def word151_5_13045 : WordLangProgHOL (BitVec 64) :=
.seq word151_5_13041 word151_2_13044

def word151_5_13049 : WordLangProgHOL (BitVec 64) :=
.seq word151_5_13045 word151_2_13048

def word151_5_13061 : WordLangProgHOL (BitVec 64) :=
.seq word151_5_13049 word151_2_13060

def word151_5_13063 : WordLangProgHOL (BitVec 64) :=
.seq word151_5_13061 word151_2_13062

def word151_5_13067 : WordLangProgHOL (BitVec 64) :=
.seq word151_5_13063 word151_2_13066

def word151_5_13069 : WordLangProgHOL (BitVec 64) :=
.seq word151_5_13067 word151_2_13068

def word151_5_13073 : WordLangProgHOL (BitVec 64) :=
.seq word151_5_13069 word151_2_13072

def word151_5_13074 : WordLangProgHOL (BitVec 64) :=
.seq word151_2_0 word151_5_13073

def pass151_5 : WordLangProgHOL (BitVec 64) :=
word151_5_13074
theorem pass151_5_eq : WordCopy.copyProp (pass151_4) = pass151_5 := by
  kernel_rfl
#print axioms pass151_5_eq
end InitECandidate.Proofs.WordStages
