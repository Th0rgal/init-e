import InitECandidate.Proofs.CompactComputation
import InitECandidate.Proofs.WordStages.Pass796_4
import InitECandidate.Proofs.CompilerComputation
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open scoped InitECandidate.Proofs.CompilerComputation
open Flapjack Flapjack.Compiler.Backend Flapjack.Compiler.Encoders.RiscV.Target
namespace InitECandidate.Proofs.WordStages
def word796_5_1937 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.move 0 [(12525, 12521)]

def word796_5_1939 : WordLangProgHOL (BitVec 64) :=
.seq word796_5_1937 word796_2_2398

def word796_5_1940 : WordLangProgHOL (BitVec 64) :=
.seq word796_4_1936 word796_5_1939

def word796_5_1942 : WordLangProgHOL (BitVec 64) :=
.seq word796_5_1940 word796_2_2401

def word796_5_1944 : WordLangProgHOL (BitVec 64) :=
.seq word796_5_1942 word796_2_2403

def word796_5_1946 : WordLangProgHOL (BitVec 64) :=
.seq word796_5_1944 word796_2_2405

def word796_5_1948 : WordLangProgHOL (BitVec 64) :=
.seq word796_5_1946 word796_2_2407

def word796_5_1950 : WordLangProgHOL (BitVec 64) :=
.seq word796_5_1948 word796_2_2409

def word796_5_1952 : WordLangProgHOL (BitVec 64) :=
.seq word796_5_1950 word796_2_2411

def word796_5_1954 : WordLangProgHOL (BitVec 64) :=
.seq word796_5_1952 word796_2_2413

def word796_5_1958 : WordLangProgHOL (BitVec 64) :=
.seq word796_5_1954 word796_2_2417

def word796_5_1960 : WordLangProgHOL (BitVec 64) :=
.seq word796_5_1958 word796_2_2419

def word796_5_1964 : WordLangProgHOL (BitVec 64) :=
.seq word796_5_1960 word796_2_2423

def word796_5_1966 : WordLangProgHOL (BitVec 64) :=
.seq word796_5_1964 word796_2_2425

def word796_5_1970 : WordLangProgHOL (BitVec 64) :=
.seq word796_5_1966 word796_2_2429

def word796_5_1972 : WordLangProgHOL (BitVec 64) :=
.seq word796_5_1970 word796_2_2431

def word796_5_1976 : WordLangProgHOL (BitVec 64) :=
.seq word796_5_1972 word796_2_2435

def word796_5_1978 : WordLangProgHOL (BitVec 64) :=
.seq word796_5_1976 word796_2_2437

def word796_5_1982 : WordLangProgHOL (BitVec 64) :=
.seq word796_5_1978 word796_2_2441

def word796_5_1984 : WordLangProgHOL (BitVec 64) :=
.seq word796_5_1982 word796_2_2443

def word796_5_1988 : WordLangProgHOL (BitVec 64) :=
.seq word796_5_1984 word796_2_2447

def word796_5_1992 : WordLangProgHOL (BitVec 64) :=
.seq word796_5_1988 word796_2_2451

def word796_5_1994 : WordLangProgHOL (BitVec 64) :=
.seq word796_5_1992 word796_2_2453

def word796_5_1996 : WordLangProgHOL (BitVec 64) :=
.seq word796_5_1994 word796_2_2455

def word796_5_1998 : WordLangProgHOL (BitVec 64) :=
.seq word796_5_1996 word796_2_2457

def word796_5_2000 : WordLangProgHOL (BitVec 64) :=
.seq word796_5_1998 word796_2_2459

def word796_5_2002 : WordLangProgHOL (BitVec 64) :=
.seq word796_5_2000 word796_2_2461

def word796_5_2004 : WordLangProgHOL (BitVec 64) :=
.seq word796_5_2002 word796_2_2463

def word796_5_2006 : WordLangProgHOL (BitVec 64) :=
.seq word796_5_2004 word796_2_2465

def word796_5_2010 : WordLangProgHOL (BitVec 64) :=
.seq word796_5_2006 word796_2_2469

def word796_5_2012 : WordLangProgHOL (BitVec 64) :=
.seq word796_5_2010 word796_2_2471

def word796_5_2016 : WordLangProgHOL (BitVec 64) :=
.seq word796_5_2012 word796_2_2475

def word796_5_2018 : WordLangProgHOL (BitVec 64) :=
.seq word796_5_2016 word796_2_2477

def word796_5_2022 : WordLangProgHOL (BitVec 64) :=
.seq word796_5_2018 word796_2_2481

def word796_5_2024 : WordLangProgHOL (BitVec 64) :=
.seq word796_5_2022 word796_2_2483

def word796_5_2028 : WordLangProgHOL (BitVec 64) :=
.seq word796_5_2024 word796_2_2487

def word796_5_2030 : WordLangProgHOL (BitVec 64) :=
.seq word796_5_2028 word796_2_2489

def word796_5_2034 : WordLangProgHOL (BitVec 64) :=
.seq word796_5_2030 word796_2_2493

def word796_5_2036 : WordLangProgHOL (BitVec 64) :=
.seq word796_5_2034 word796_2_2495

def word796_5_2040 : WordLangProgHOL (BitVec 64) :=
.seq word796_5_2036 word796_2_2499

def word796_5_2042 : WordLangProgHOL (BitVec 64) :=
.seq word796_5_2040 word796_2_2501

def word796_5_2046 : WordLangProgHOL (BitVec 64) :=
.seq word796_5_2042 word796_2_2505

def word796_5_2047 : WordLangProgHOL (BitVec 64) :=
.seq word796_2_0 word796_5_2046

def pass796_5 : WordLangProgHOL (BitVec 64) :=
word796_5_2047
theorem pass796_5_eq : WordCopy.copyProp (pass796_4) = pass796_5 := by
  kernel_rfl
#print axioms pass796_5_eq
end InitECandidate.Proofs.WordStages
