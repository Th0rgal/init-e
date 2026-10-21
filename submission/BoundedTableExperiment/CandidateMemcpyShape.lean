import InitECandidate.Runtime.PanStatementWork
import InitECandidate.Proofs.FrontendCodecComputation
import CandidateAst

namespace BoundedTableExperiment
open InitECandidate.Runtime
open InitECandidate.Runtime.FineCost
open Flapjack
open Flapjack.Pancake.PanLang
open Flapjack.PanSemStateFiniteExact
open InitECandidate.Proofs.FrontendCodecComputation
open Flapjack.Basis.Pure.MlString

set_option maxRecDepth 100000
set_option maxHeartbeats 1000000

/-! ## expression helpers -/

def loc (n : String) : ExpHOL 64 := .var .local (ofString n)
def off (n : String) (d : BitVec 64) : ExpHOL 64 := .op .add [loc n,.const d]
def lw (e : ExpHOL 64) : ExpHOL 64 := .load .one e

/-- `base + index` (no offset). -/
def plus (b i : ExpHOL 64) : ExpHOL 64 := .op .add [b,i]
/-- `base + index` written with two `BinOp.add` arguments (offset 0 in the AST). -/
def ato0 (b i : String) : ExpHOL 64 := .op .add [loc b,loc i]
/-- `base + index + d` (three-argument `BinOp.add` in the AST). -/
def ato (b i : String) (d : BitVec 64) : ExpHOL 64 := .op .add [loc b,loc i,.const d]
/-- `i + k`. -/
def bump (i : String) (d : BitVec 64) : ExpHOL 64 := .op .add [loc i,.const d]

/-! ## `memcpy`: 32-byte, 8-byte word, 8-byte unaligned byte, then residual byte loops -/

def memcpyBump32 : ProgHOL 64 := .assign .local (ofString "i") (bump "i" 32)
def memcpyBump8 : ProgHOL 64 := .assign .local (ofString "i") (bump "i" 8)
def memcpyBump1 : ProgHOL 64 := .assign .local (ofString "i") (bump "i" 1)

def memcpyStoreWord0 : ProgHOL 64 :=
  .store (ato0 "dst" "i") (lw (ato0 "src" "i"))

def memcpyStoreWord (d : BitVec 64) : ProgHOL 64 :=
  .store (ato "dst" "i" d) (lw (ato "src" "i" d))

def memcpyStoreByte0 : ProgHOL 64 :=
  .storeByte (ato0 "dst" "i") (.loadByte (ato0 "src" "i"))

def memcpyStoreByte (d : BitVec 64) : ProgHOL 64 :=
  .storeByte (ato "dst" "i" d) (.loadByte (ato "src" "i" d))

/-- One 32-byte iteration: four word copies, then `i += 32`. -/
def memcpyStep32 : ProgHOL 64 :=
  .seq memcpyStoreWord0
    (.seq (memcpyStoreWord 8)
      (.seq (memcpyStoreWord 16) (.seq (memcpyStoreWord 24) memcpyBump32)))

/-- One 8-byte iteration of the unaligned path: eight byte copies, then `i += 8`. -/
def memcpyStep8Bytes : ProgHOL 64 :=
  .seq memcpyStoreByte0
    (.seq (memcpyStoreByte 1)
      (.seq (memcpyStoreByte 2)
        (.seq (memcpyStoreByte 3)
          (.seq (memcpyStoreByte 4)
            (.seq (memcpyStoreByte 5) (.seq (memcpyStoreByte 6) (.seq (memcpyStoreByte 7) memcpyBump8)))))))

def memcpyWhile32 : ProgHOL 64 :=
  .while (.cmp .notLower (loc "n") (bump "i" 32)) memcpyStep32

def memcpyWhile8 : ProgHOL 64 :=
  .while (.cmp .notLower (loc "n") (bump "i" 8))
    (.seq memcpyStoreWord0 memcpyBump8)

def memcpyWhile8Bytes : ProgHOL 64 :=
  .while (.cmp .notLower (loc "n") (bump "i" 8)) memcpyStep8Bytes

def memcpyWhileByte : ProgHOL 64 :=
  .while (.cmp .lower (loc "i") (loc "n"))
    (.seq memcpyStoreByte0 memcpyBump1)

def memcpyReturn : ProgHOL 64 := .return (.const 0)

/-- `(dst | src) & 7 == 0`. -/
def memcpyAligned : ExpHOL 64 :=
  .cmp .equal (.op .and [.op .or [loc "dst",loc "src"],.const 7]) (.const 0)

def memcpyBody : ProgHOL 64 :=
  .dec (ofString "i") .one (.const 0)
    (.seq (.ite memcpyAligned (.seq memcpyWhile32 memcpyWhile8) .skip)
      (.seq memcpyWhile8Bytes (.seq memcpyWhileByte memcpyReturn)))

/-! ## `memzero`: same shape, zero stores -/

def memzeroStoreWord0 : ProgHOL 64 := .store (ato0 "dst" "i") (.const 0)
def memzeroStoreWord (d : BitVec 64) : ProgHOL 64 := .store (ato "dst" "i" d) (.const 0)
def memzeroStoreByte0 : ProgHOL 64 := .storeByte (ato0 "dst" "i") (.const 0)
def memzeroStoreByte (d : BitVec 64) : ProgHOL 64 := .storeByte (ato "dst" "i" d) (.const 0)

def memzeroStep32 : ProgHOL 64 :=
  .seq memzeroStoreWord0
    (.seq (memzeroStoreWord 8)
      (.seq (memzeroStoreWord 16) (.seq (memzeroStoreWord 24) memcpyBump32)))

def memzeroStep8Bytes : ProgHOL 64 :=
  .seq memzeroStoreByte0
    (.seq (memzeroStoreByte 1)
      (.seq (memzeroStoreByte 2)
        (.seq (memzeroStoreByte 3)
          (.seq (memzeroStoreByte 4)
            (.seq (memzeroStoreByte 5) (.seq (memzeroStoreByte 6) (.seq (memzeroStoreByte 7) memcpyBump8)))))))

def memzeroWhile32 : ProgHOL 64 :=
  .while (.cmp .notLower (loc "n") (bump "i" 32)) memzeroStep32

def memzeroWhile8 : ProgHOL 64 :=
  .while (.cmp .notLower (loc "n") (bump "i" 8))
    (.seq memzeroStoreWord0 memcpyBump8)

def memzeroWhile8Bytes : ProgHOL 64 :=
  .while (.cmp .notLower (loc "n") (bump "i" 8)) memzeroStep8Bytes

def memzeroWhileByte : ProgHOL 64 :=
  .while (.cmp .lower (loc "i") (loc "n"))
    (.seq memzeroStoreByte0 memcpyBump1)

def memzeroReturn : ProgHOL 64 := .return (.const 0)

/-- `dst & 7 == 0`. -/
def memzeroAligned : ExpHOL 64 :=
  .cmp .equal (.op .and [loc "dst",.const 7]) (.const 0)

def memzeroBody : ProgHOL 64 :=
  .dec (ofString "i") .one (.const 0)
    (.seq (.ite memzeroAligned (.seq memzeroWhile32 memzeroWhile8) .skip)
      (.seq memzeroWhile8Bytes (.seq memzeroWhileByte memzeroReturn)))

/-! ## the pinning theorems -/

/-- (1) The whole `memcpy` body. -/
theorem candidateMemcpy_body :
    sourceFunctionBody Candidate.guestFn_memcpy = memcpyBody := by
  simp only [sourceFunctionBody, declToHOL_eq, declToHOLStructural, funDeclToHOLStructural,
    Candidate.guestFn_memcpy, memcpyBody, memcpyAligned, memcpyWhile32, memcpyWhile8,
    memcpyWhile8Bytes, memcpyWhileByte, memcpyReturn, memcpyStep32, memcpyStep8Bytes,
    memcpyStoreWord, memcpyStoreByte, memcpyBump32, memcpyBump8, memcpyBump1,
    loc, lw, ato0, ato, bump, memcpyStoreWord0, memcpyStoreByte0,
    progToHOLStructural, expToHOLStructural, expListToHOLStructural, shapeToHOLStructural,
    paramToHOLStructural, List.map_cons, List.map_nil]
  rfl

/-- (1') The same with the scopes and loops spelled out. -/
theorem candidateMemcpy_body_scopes :
    sourceFunctionBody Candidate.guestFn_memcpy =
      .dec (ofString "i") .one (.const 0)
        (.seq
          (.ite (.cmp .equal (.op .and [.op .or [loc "dst",loc "src"],.const 7]) (.const 0))
            (.seq memcpyWhile32 memcpyWhile8) .skip)
          (.seq memcpyWhile8Bytes (.seq memcpyWhileByte memcpyReturn))) :=
  candidateMemcpy_body

/-- The alignment test is `(dst | src) & 7 == 0`. -/
theorem candidateMemcpy_aligned :
    memcpyAligned = .cmp .equal (.op .and [.op .or [loc "dst",loc "src"],.const 7]) (.const 0) := rfl

/-- (2) The three memcpy loops and the return. -/
theorem candidateMemcpy_while32 :
    memcpyWhile32 = .while (.cmp .notLower (loc "n") (.op .add [loc "i",.const 32])) memcpyStep32 := rfl

theorem candidateMemcpy_step32 :
    memcpyStep32 =
      .seq memcpyStoreWord0
        (.seq (.store (ato "dst" "i" 8) (lw (ato "src" "i" 8)))
          (.seq (.store (ato "dst" "i" 16) (lw (ato "src" "i" 16)))
            (.seq (.store (ato "dst" "i" 24) (lw (ato "src" "i" 24))) memcpyBump32))) := rfl

theorem candidateMemcpy_bump32 :
    memcpyBump32 = .assign .local (ofString "i") (.op .add [loc "i",.const 32]) := rfl

theorem candidateMemcpy_while8 :
    memcpyWhile8 =
      .while (.cmp .notLower (loc "n") (.op .add [loc "i",.const 8]))
        (.seq memcpyStoreWord0 memcpyBump8) := rfl

theorem candidateMemcpy_while8Bytes :
    memcpyWhile8Bytes =
      .while (.cmp .notLower (loc "n") (.op .add [loc "i",.const 8])) memcpyStep8Bytes := rfl

theorem candidateMemcpy_whileByte :
    memcpyWhileByte =
      .while (.cmp .lower (loc "i") (loc "n"))
        (.seq memcpyStoreByte0 memcpyBump1) := rfl

theorem candidateMemcpy_bump1 :
    memcpyBump1 = .assign .local (ofString "i") (.op .add [loc "i",.const 1]) := rfl

theorem candidateMemcpy_return : memcpyReturn = .return (.const 0) := rfl

/-! ## memzero -/

theorem candidateMemzero_body :
    sourceFunctionBody Candidate.guestFn_memzero = memzeroBody := by
  simp only [sourceFunctionBody, declToHOL_eq, declToHOLStructural, funDeclToHOLStructural,
    Candidate.guestFn_memzero, memzeroBody, memzeroAligned, memzeroWhile32, memzeroWhile8,
    memzeroWhile8Bytes, memzeroWhileByte, memzeroReturn, memzeroStep32, memzeroStep8Bytes,
    memzeroStoreWord, memzeroStoreByte, memcpyBump32, memcpyBump8, memcpyBump1,
    loc, lw, ato0, ato, bump, memcpyStoreWord0, memcpyStoreByte0, memzeroStoreWord0, memzeroStoreByte0,
    progToHOLStructural, expToHOLStructural, expListToHOLStructural, shapeToHOLStructural,
    paramToHOLStructural, List.map_cons, List.map_nil, Option.map]
  rfl

theorem candidateMemzero_while32 :
    memzeroWhile32 = .while (.cmp .notLower (loc "n") (.op .add [loc "i",.const 32])) memzeroStep32 := rfl

theorem candidateMemzero_step32 :
    memzeroStep32 =
      .seq memzeroStoreWord0
        (.seq (.store (ato "dst" "i" 8) (.const 0))
          (.seq (.store (ato "dst" "i" 16) (.const 0))
            (.seq (.store (ato "dst" "i" 24) (.const 0)) memcpyBump32))) := rfl

theorem candidateMemzero_while8 :
    memzeroWhile8 =
      .while (.cmp .notLower (loc "n") (.op .add [loc "i",.const 8]))
        (.seq memzeroStoreWord0 memcpyBump8) := rfl

theorem candidateMemzero_whileByte :
    memzeroWhileByte =
      .while (.cmp .lower (loc "i") (loc "n"))
        (.seq memzeroStoreByte0 memcpyBump1) := rfl

theorem candidateMemzero_return : memzeroReturn = .return (.const 0) := rfl

end BoundedTableExperiment

#print axioms BoundedTableExperiment.candidateMemcpy_body
#print axioms BoundedTableExperiment.candidateMemzero_body
