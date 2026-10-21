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

/-- `t + offset`. -/
def localAddr (name : MlS) (offset : BitVec 64) : ExpHOL 64 :=
  .op .add [.var .local name,.const offset]

/-! ## `htab_find_leaf_path`, built bottom up.  Theorem
`candidateFindLeaf_body` below is what pins these definitions to the AST. -/

/-- The child choice. -/
def candidateFindLeafChild : ProgHOL 64 :=
  .ite (.cmp .notEqual (.op .and [.var .local (ofString "b"),.var .local (ofString "m")])
      (.const (0 : BitVec 64)))
    (.assign .local (ofString "node") (.load .one (localAddr (ofString "node") 8)))
    (.assign .local (ofString "node") (.load .one (.var .local (ofString "node"))))

def candidateFindLeafMask : ProgHOL 64 :=
  .dec (ofString "m") .one (.op .xor [.var .local (ofString "route"),.const (BitVec.ofNat 64 255)])
    candidateFindLeafChild

def candidateFindLeafByte : ProgHOL 64 :=
  .dec (ofString "b") .one
    (.loadByte (.op .add [.var .local (ofString "key"),
      .shift .asr (.var .local (ofString "route")) (.const (BitVec.ofNat 64 8))]))
    candidateFindLeafMask

/-- `dec route = load (node + 16)`, then the byte, mask and child choice. -/
def candidateFindLeafRoute : ProgHOL 64 :=
  .dec (ofString "route") .one (.load .one (localAddr (ofString "node") 16))
    candidateFindLeafByte

def candidateFindLeafPush : ProgHOL 64 :=
  .store (.op .add [.var .local (ofString "path"),
      .panop .mul [.var .local (ofString "depth"),.const (BitVec.ofNat 64 8)]])
    (.var .local (ofString "node"))

def candidateFindLeafBump : ProgHOL 64 :=
  .assign .local (ofString "depth")
    (.op .add [.var .local (ofString "depth"),.const (BitVec.ofNat 64 1)])

/-- Iteration body after the guard. -/
def candidateFindLeafWalk : ProgHOL 64 :=
  .seq candidateFindLeafPush (.seq candidateFindLeafBump candidateFindLeafRoute)

/-- Iteration head: early return when the table is above threshold. -/
def candidateFindLeafGuard : ProgHOL 64 :=
  .ite (.cmp .notLower (.var .local (ofString "cap")) (.var .local (ofString "node")))
    (.seq (.store (localAddr (ofString "t") 112) (.var .local (ofString "depth")))
      (.return (.var .local (ofString "node"))))
    .skip

/-- One iteration of the loop. -/
def candidateFindLeafStep : ProgHOL 64 :=
  .seq candidateFindLeafGuard candidateFindLeafWalk

/-- The loop. -/
def candidateFindLeafLoop : ProgHOL 64 :=
  .while (.cmp .notEqual (.var .local (ofString "node")) (.const (0 : BitVec 64)))
    candidateFindLeafStep

/-- What runs after the loop: store the depth, return 0. -/
def candidateFindLeafTail : ProgHOL 64 :=
  .seq (.store (localAddr (ofString "t") 112) (.var .local (ofString "depth")))
    (.return (.const (0 : BitVec 64)))

/-- The whole body: four scopes, then loop and tail. -/
def candidateFindLeafBody : ProgHOL 64 :=
  .dec (ofString "cap") .one (.load .one (localAddr (ofString "t") 16))
    (.dec (ofString "path") .one (.load .one (localAddr (ofString "t") 104))
      (.dec (ofString "node") .one (.load .one (localAddr (ofString "t") 72))
        (.dec (ofString "depth") .one (.const (0 : BitVec 64))
          (.seq candidateFindLeafLoop candidateFindLeafTail))))

/-! ## the theorems -/

/-- (1) The candidate `htab_find_leaf_path` body has exactly this structure. -/
theorem candidateFindLeaf_body :
    sourceFunctionBody Candidate.guestFn_htab_find_leaf_path = candidateFindLeafBody := by
  simp only [sourceFunctionBody, declToHOL_eq, declToHOLStructural, funDeclToHOLStructural,
    Candidate.guestFn_htab_find_leaf_path, candidateFindLeafBody, candidateFindLeafLoop,
    candidateFindLeafTail, candidateFindLeafStep, candidateFindLeafGuard,
    candidateFindLeafWalk, candidateFindLeafRoute, candidateFindLeafByte,
    candidateFindLeafMask, candidateFindLeafChild, candidateFindLeafPush,
    candidateFindLeafBump, localAddr,
    progToHOLStructural, expToHOLStructural, expListToHOLStructural, shapeToHOLStructural,
    paramToHOLStructural, List.map_cons, List.map_nil]
  rfl

/-- (1') The same, with the shape of the leading scopes spelled out. -/
theorem candidateFindLeaf_body_scopes :
    sourceFunctionBody Candidate.guestFn_htab_find_leaf_path =
      .dec (ofString "cap") .one (.load .one (localAddr (ofString "t") 16))
        (.dec (ofString "path") .one (.load .one (localAddr (ofString "t") 104))
          (.dec (ofString "node") .one (.load .one (localAddr (ofString "t") 72))
            (.dec (ofString "depth") .one (.const (0 : BitVec 64))
              (.seq candidateFindLeafLoop candidateFindLeafTail)))) :=
  candidateFindLeaf_body

/-- (2) `loop = while (node != 0) step`. -/
theorem candidateFindLeaf_loop :
    candidateFindLeafLoop =
      .while (.cmp .notEqual (.var .local (ofString "node")) (.const (0 : BitVec 64)))
        candidateFindLeafStep := rfl

/-- (3) `tail = seq (store (t + 112) depth) (return 0)`. -/
theorem candidateFindLeaf_tail :
    candidateFindLeafTail =
      .seq (.store (localAddr (ofString "t") 112) (.var .local (ofString "depth")))
        (.return (.const (0 : BitVec 64))) := rfl

/-- (4) `step = seq (ite (cap >= node) (seq (store (t+112) depth) (return node)) skip) walk`. -/
theorem candidateFindLeaf_step :
    candidateFindLeafStep =
      .seq
        (.ite (.cmp .notLower (.var .local (ofString "cap")) (.var .local (ofString "node")))
          (.seq (.store (localAddr (ofString "t") 112) (.var .local (ofString "depth")))
            (.return (.var .local (ofString "node"))))
          .skip)
        candidateFindLeafWalk := rfl

theorem candidateFindLeaf_walk :
    candidateFindLeafWalk =
      .seq candidateFindLeafPush (.seq candidateFindLeafBump candidateFindLeafRoute) := rfl

theorem candidateFindLeaf_route :
    candidateFindLeafRoute =
      .dec (ofString "route") .one (.load .one (localAddr (ofString "node") 16))
        candidateFindLeafByte := rfl

theorem candidateFindLeaf_child :
    candidateFindLeafChild =
      .ite (.cmp .notEqual (.op .and [.var .local (ofString "b"),.var .local (ofString "m")])
          (.const (0 : BitVec 64)))
        (.assign .local (ofString "node") (.load .one (localAddr (ofString "node") 8)))
        (.assign .local (ofString "node") (.load .one (.var .local (ofString "node")))) := rfl

/-- `cases` on a `StatementRun` of the find_leaf_path body exposes the scopes. -/
example {F : Type} (fn : MlS) (s : PanSemStateFiniteExact 64 F)
    (r : Option (PanSemResultExact 64)) (post : PanSemStateFiniteExact 64 F)
    (ev : List WorkEvent)
    (run : StatementRun fn s (sourceFunctionBody Candidate.guestFn_htab_find_leaf_path) r post ev) :
    True := by
  rw [candidateFindLeaf_body_scopes] at run
  cases run with
  | declareValue _ _ rest => trivial
  | declareMismatch _ _ => trivial
  | declareFailure _ => trivial

end BoundedTableExperiment

#print axioms BoundedTableExperiment.candidateFindLeaf_body
#print axioms BoundedTableExperiment.candidateFindLeaf_body_scopes
#print axioms BoundedTableExperiment.candidateFindLeaf_loop
#print axioms BoundedTableExperiment.candidateFindLeaf_step
#print axioms BoundedTableExperiment.candidateFindLeaf_route
#print axioms BoundedTableExperiment.candidateFindLeaf_child
