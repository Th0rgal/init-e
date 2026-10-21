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
def idx8 (base index : ExpHOL 64) : ExpHOL 64 := .op .add [base,.panop .mul [index,.const 8]]

/-! ## the duplicate check (first arm of the `htab_set` body) -/

def candidateHtabSetValueStore : ProgHOL 64 :=
  .seq (.store (idx8 (lw (off "t" 40)) (.op .sub [loc "leaf",.const 1])) (loc "value"))
    (.return (.const 0))

def candidateHtabSetEqBranch : ProgHOL 64 :=
  .ite (.cmp .notEqual (loc "eq") (.const 0)) candidateHtabSetValueStore .skip

def candidateHtabSetEqChain : ProgHOL 64 :=
  .decCall (ofString "eq") .one (ofString "memeq")
    [loc "kp",loc "key",lw (off "t" 0)] candidateHtabSetEqBranch

def candidateHtabSetKpChain : ProgHOL 64 :=
  .decCall (ofString "kp") .one (ofString "htab_key_ptr") [loc "t",loc "leaf"]
    candidateHtabSetEqChain

/-- The duplicate check: `if leaf != 0 then (check key, store value if equal)`. -/
def candidateHtabSetDuplicate : ProgHOL 64 :=
  .ite (.cmp .notEqual (loc "leaf") (.const 0)) candidateHtabSetKpChain .skip

/-! ## the insertion tail (second arm of the `htab_set` body) -/

def candidateHtabSetGrowSeq : ProgHOL 64 :=
  .seq (.call (some (none, none)) (ofString "htab_grow") [loc "t"])
    (.seq (.assign .local (ofString "cap") (lw (off "t" 16)))
      (.call (some (some (.local, ofString "leaf"), none)) (ofString "htab_find_leaf_path")
        [loc "t",loc "key"]))

/-- Growth branch: grow, refresh `cap`, then re-find the leaf. -/
def candidateHtabSetGrowth : ProgHOL 64 :=
  .ite (.cmp .lower (loc "cap")
      (.panop .mul [.op .add [lw (off "t" 24),.const 1],.const 2]))
    candidateHtabSetGrowSeq .skip

/-- `path[mid] + 16`: the 16-byte records of the internal nodes. -/
def candidateHtabSetMrAddr : ExpHOL 64 :=
  .op .add [lw (idx8 (loc "path") (loc "mid")),.const 16]

/-- Binary search for the insertion depth. -/
def candidateHtabSetBsearch : ProgHOL 64 :=
  .while (.cmp .less (loc "lo") (loc "hi"))
    (.dec (ofString "mid") .one (.shift .asr (.op .add [loc "lo",loc "hi"]) (.const 1))
      (.dec (ofString "mr") .one (lw candidateHtabSetMrAddr)
        (.ite (.cmp .lower (loc "d") (loc "mr"))
          (.assign .local (ofString "hi") (loc "mid"))
          (.assign .local (ofString "lo") (.op .add [loc "mid",.const 1])))))

def candidateHtabSetCurIte : ProgHOL 64 :=
  .ite (.cmp .notEqual (loc "lo") (loc "depth")) (.assign .local (ofString "cur") (lw (idx8 (loc "path") (loc "lo"))))
    .skip

def candidateHtabSetParentIte : ProgHOL 64 :=
  .ite (.cmp .notEqual (loc "lo") (.const 0))
    (.assign .local (ofString "parent") (lw (idx8 (loc "path") (.op .sub [loc "lo",.const 1]))))
    .skip

def candidateHtabSetDirAssign : ProgHOL 64 :=
  .ite (.cmp .notEqual (.op .and [loc "pb",loc "pm"]) (.const 0))
    (.assign .local (ofString "dir") (.const 1)) .skip

def candidateHtabSetPmChain : ProgHOL 64 :=
  .dec (ofString "pm") .one (.op .xor [loc "pr",.const (BitVec.ofNat 64 255)])
    candidateHtabSetDirAssign

def candidateHtabSetPbChain : ProgHOL 64 :=
  .dec (ofString "pb") .one
    (.loadByte (.op .add [loc "key",.shift .asr (loc "pr") (.const (BitVec.ofNat 64 8))]))
    candidateHtabSetPmChain

def candidateHtabSetPrChain : ProgHOL 64 :=
  .dec (ofString "pr") .one (lw (.op .add [loc "parent",.const 16])) candidateHtabSetPbChain

/-- Direction of the new branch below `parent`. -/
def candidateHtabSetDirIte : ProgHOL 64 :=
  .ite (.cmp .notEqual (loc "parent") (.const 0)) candidateHtabSetPrChain .skip

def candidateHtabSetSideStores : ProgHOL 64 :=
  .ite (.cmp .notEqual (loc "side") (.const 0))
    (.seq (.store (loc "nip") (loc "cur")) (.store (off "nip" 8) (loc "new_leaf")))
    (.seq (.store (loc "nip") (loc "new_leaf")) (.store (off "nip" 8) (loc "cur")))

def candidateHtabSetPpIte : ProgHOL 64 :=
  .ite (.cmp .notEqual (loc "dir") (.const 0)) (.store (off "pp" 8) (loc "new_int"))
    (.store (loc "pp") (loc "new_int"))

/-- Where the new internal node is hung: the root slot or a `parent` child slot. -/
def candidateHtabSetLink : ProgHOL 64 :=
  .ite (.cmp .equal (loc "parent") (.const 0)) (.store (off "t" 72) (loc "new_int"))
    (.dec (ofString "pp") .one (loc "parent") candidateHtabSetPpIte)

def candidateHtabSetPosSeq : ProgHOL 64 :=
  .seq (.store (idx8 (lw (off "t" 56)) (loc "pos")) (loc "new_leaf"))
    (.seq (.store (idx8 (lw (off "t" 64)) (.op .sub [loc "new_leaf",.const 1])) (loc "pos"))
      (.seq (.store (off "t" 24) (.op .add [loc "pos",.const 1]))
        (.return (.const 0))))

def candidateHtabSetPosBlock : ProgHOL 64 :=
  .dec (ofString "pos") .one (lw (off "t" 24)) candidateHtabSetPosSeq

def candidateHtabSetSideChain : ProgHOL 64 :=
  .decCall (ofString "side") .one (ofString "htab_bit") [loc "key",loc "d"]
    (.seq candidateHtabSetSideStores (.seq candidateHtabSetLink candidateHtabSetPosBlock))

def candidateHtabSetNipBlock : ProgHOL 64 :=
  .dec (ofString "nip") .one (loc "new_int") candidateHtabSetSideChain

def candidateHtabSetDirSeq : ProgHOL 64 :=
  .seq candidateHtabSetDirIte candidateHtabSetNipBlock

def candidateHtabSetDirBlock : ProgHOL 64 :=
  .dec (ofString "dir") .one (.const 0) candidateHtabSetDirSeq

def candidateHtabSetParentSeq : ProgHOL 64 :=
  .seq candidateHtabSetParentIte candidateHtabSetDirBlock

def candidateHtabSetCurSeq : ProgHOL 64 :=
  .seq candidateHtabSetCurIte candidateHtabSetParentSeq

def candidateHtabSetCurBlock : ProgHOL 64 :=
  .dec (ofString "cur") .one (loc "leaf") candidateHtabSetCurSeq

def candidateHtabSetParentBlock : ProgHOL 64 :=
  .dec (ofString "parent") .one (.const 0) candidateHtabSetCurBlock

def candidateHtabSetSearch : ProgHOL 64 :=
  .seq candidateHtabSetBsearch candidateHtabSetParentBlock

def candidateHtabSetHiBlock : ProgHOL 64 :=
  .dec (ofString "hi") .one (loc "depth") candidateHtabSetSearch

def candidateHtabSetLoBlock : ProgHOL 64 :=
  .dec (ofString "lo") .one (.const 0) candidateHtabSetHiBlock

def candidateHtabSetDepthBlock : ProgHOL 64 :=
  .dec (ofString "depth") .one (lw (off "t" 112)) candidateHtabSetLoBlock

def candidateHtabSetPathBlock : ProgHOL 64 :=
  .dec (ofString "path") .one (lw (off "t" 104)) candidateHtabSetDepthBlock

def candidateHtabSetNewIntChain : ProgHOL 64 :=
  .decCall (ofString "new_int") .one (ofString "htab_new_internal") [loc "t",loc "d"]
    candidateHtabSetPathBlock

def candidateHtabSetNewLeafChain : ProgHOL 64 :=
  .decCall (ofString "new_leaf") .one (ofString "htab_new_leaf") [loc "t",loc "key",loc "value"]
    candidateHtabSetNewIntChain

def candidateHtabSetDChain : ProgHOL 64 :=
  .decCall (ofString "d") .one (ofString "htab_first_diff") [loc "key",loc "kp",lw (off "t" 0)]
    candidateHtabSetNewLeafChain

/-- Re-key the found leaf and split the new leaf/internal node off it. -/
def candidateHtabSetBsearchLink : ProgHOL 64 :=
  .decCall (ofString "kp") .one (ofString "htab_key_ptr") [loc "t",loc "leaf"] candidateHtabSetDChain

/-- The insertion tail: growth branch, then the binary-search link. -/
def candidateHtabSetInsertionTail : ProgHOL 64 :=
  .seq candidateHtabSetGrowth candidateHtabSetBsearchLink


/-! ## the fresh-leaf arm of the `htab_set` body (the `only` branch) -/

def candidateHtabSetOnlySeq : ProgHOL 64 :=
  .seq (.store (off "t" 72) (loc "only"))
    (.seq (.store (lw (off "t" 56)) (loc "only"))
      (.seq (.store (idx8 (lw (off "t" 64)) (.op .sub [loc "only",.const 1])) (.const 0))
        (.seq (.store (off "t" 24) (.const 1)) (.return (.const 0)))))

def candidateHtabSetOnlyChain : ProgHOL 64 :=
  .decCall (ofString "only") .one (ofString "htab_new_leaf") [loc "t",loc "key",loc "value"]
    candidateHtabSetOnlySeq

/-- The empty-table arm: allocate the first leaf and return. -/
def candidateHtabSetMiss : ProgHOL 64 :=
  .ite (.cmp .equal (lw (off "t" 72)) (.const 0)) candidateHtabSetOnlyChain .skip

/-- The body of `decCall leaf (htab_find_leaf_path …)`: duplicate check, then insertion. -/
def candidateHtabSetLeafBody : ProgHOL 64 :=
  .seq candidateHtabSetDuplicate candidateHtabSetInsertionTail

/-- (1) Body shape: duplicate check followed by the insertion tail. -/
theorem candidateHtabSetLeaf_body :
    candidateHtabSetLeafBody =
      .seq candidateHtabSetDuplicate candidateHtabSetInsertionTail := rfl

/-- The `decCall leaf ("htab_find_leaf_path")` node inside the candidate `htab_set`. -/
theorem candidateHtabSetLeaf_decCall :
    sourceFunctionBody Candidate.guestFn_htab_set =
      .dec (ofString "cap") .one (lw (off "t" 16))
        (.seq candidateHtabSetMiss
          (.decCall (ofString "leaf") .one (ofString "htab_find_leaf_path")
            [loc "t",loc "key"] candidateHtabSetLeafBody)) := by
  simp only [sourceFunctionBody, declToHOL_eq, declToHOLStructural, funDeclToHOLStructural,
    Candidate.guestFn_htab_set,
    candidateHtabSetLeafBody, candidateHtabSetDuplicate, candidateHtabSetInsertionTail,
    candidateHtabSetBsearchLink,
    candidateHtabSetMiss, candidateHtabSetOnlyChain, candidateHtabSetOnlySeq,
    candidateHtabSetKpChain, candidateHtabSetEqChain, candidateHtabSetEqBranch,
    candidateHtabSetValueStore,
    candidateHtabSetGrowth, candidateHtabSetGrowSeq, candidateHtabSetBsearch,
    candidateHtabSetMrAddr, candidateHtabSetSearch, candidateHtabSetParentBlock,
    candidateHtabSetCurBlock, candidateHtabSetCurSeq, candidateHtabSetCurIte,
    candidateHtabSetParentSeq, candidateHtabSetParentIte, candidateHtabSetDirBlock,
    candidateHtabSetDirSeq, candidateHtabSetDirIte, candidateHtabSetPrChain,
    candidateHtabSetPbChain, candidateHtabSetPmChain, candidateHtabSetDirAssign,
    candidateHtabSetNipBlock, candidateHtabSetSideChain, candidateHtabSetSideStores,
    candidateHtabSetLink, candidateHtabSetPpIte, candidateHtabSetPosBlock,
    candidateHtabSetPosSeq, candidateHtabSetHiBlock, candidateHtabSetLoBlock,
    candidateHtabSetDepthBlock, candidateHtabSetPathBlock,
    candidateHtabSetNewIntChain, candidateHtabSetNewLeafChain, candidateHtabSetDChain,
    loc, off, lw, idx8,
    progToHOLStructural, expToHOLStructural, expListToHOLStructural, shapeToHOLStructural,
    paramToHOLStructural, List.map_cons, List.map_nil, Option.map]
  rfl

/-- (2) Growth branch: `if cap < (count+1)*2 then grow; cap := load (t+16); leaf := htab_find_leaf_path t key`. -/
theorem candidateHtabSetLeaf_growth :
    candidateHtabSetGrowth =
      .ite (.cmp .lower (loc "cap") (.panop .mul [.op .add [lw (off "t" 24),.const 1],.const 2]))
        (.seq (.call (some (none, none)) (ofString "htab_grow") [loc "t"])
          (.seq (.assign .local (ofString "cap") (lw (off "t" 16)))
            (.call (some (some (.local, ofString "leaf"), none)) (ofString "htab_find_leaf_path")
              [loc "t",loc "key"])))
        .skip := rfl

/-- (3) The binary-search loop. -/
theorem candidateHtabSetLeaf_bsearch :
    candidateHtabSetBsearch =
      .while (.cmp .less (loc "lo") (loc "hi"))
        (.dec (ofString "mid") .one (.shift .asr (.op .add [loc "lo",loc "hi"]) (.const 1))
          (.dec (ofString "mr") .one (lw (candidateHtabSetMrAddr))
            (.ite (.cmp .lower (loc "d") (loc "mr"))
              (.assign .local (ofString "hi") (loc "mid"))
              (.assign .local (ofString "lo") (.op .add [loc "mid",.const 1]))))) := rfl

theorem candidateHtabSetLeaf_mrAddr :
    candidateHtabSetMrAddr = .op .add [lw (idx8 (loc "path") (loc "mid")),.const 16] := rfl

/-- (4a) The two child stores of the new internal node, by `side`. -/
theorem candidateHtabSetLeaf_sideStores :
    candidateHtabSetSideStores =
      .ite (.cmp .notEqual (loc "side") (.const 0))
        (.seq (.store (loc "nip") (loc "cur")) (.store (off "nip" 8) (loc "new_leaf")))
        (.seq (.store (loc "nip") (loc "new_leaf")) (.store (off "nip" 8) (loc "cur"))) := rfl

/-- (4b) Hanging `new_int`: root slot `t+72`, else `parent`'s slot by `dir`. -/
theorem candidateHtabSetLeaf_link :
    candidateHtabSetLink =
      .ite (.cmp .equal (loc "parent") (.const 0)) (.store (off "t" 72) (loc "new_int"))
        (.dec (ofString "pp") .one (loc "parent")
          (.ite (.cmp .notEqual (loc "dir") (.const 0)) (.store (off "pp" 8) (loc "new_int"))
            (.store (loc "pp") (loc "new_int")))) := rfl

/-- (4c) The `order` bookkeeping: `order[pos] := new_leaf`, `order_pos[new_leaf-1] := pos`, `count := pos+1`. -/
theorem candidateHtabSetLeaf_posSeq :
    candidateHtabSetPosSeq =
      .seq (.store (idx8 (lw (off "t" 56)) (loc "pos")) (loc "new_leaf"))
        (.seq (.store (idx8 (lw (off "t" 64)) (.op .sub [loc "new_leaf",.const 1])) (loc "pos"))
          (.seq (.store (off "t" 24) (.op .add [loc "pos",.const 1]))
            (.return (.const 0)))) := rfl

end BoundedTableExperiment

#print axioms BoundedTableExperiment.candidateHtabSetLeaf_decCall
#print axioms BoundedTableExperiment.candidateHtabSetLeaf_growth
#print axioms BoundedTableExperiment.candidateHtabSetLeaf_bsearch
#print axioms BoundedTableExperiment.candidateHtabSetLeaf_sideStores
#print axioms BoundedTableExperiment.candidateHtabSetLeaf_link
#print axioms BoundedTableExperiment.candidateHtabSetLeaf_posSeq
