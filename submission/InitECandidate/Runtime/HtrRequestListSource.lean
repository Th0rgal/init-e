import InitECandidate.Runtime.RecordHashSource
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
set_option maxRecDepth 100000

def htrRequestListAt (index : Nat) : ProgHOL 64 :=
  (statelessNext^[index]) (structuralFunctionBody Guest.guestFn_htr_request_list)

def htrRequestListArguments : List (ExpHOL 64) :=
  [.op .add [.var .local (ofString "p"),.panop .mul [.var .local (ofString "i"),.var .local (ofString "sz")]],
   .op .add [.var .local (ofString "roots"),.panop .mul [.var .local (ofString "i"),.const 32]]]

def htrRequestListBranch (kind : BitVec 64) (function : MlS) : ProgHOL 64 :=
  .ite (.cmp .equal (.var .local (ofString "kind")) (.const kind))
    (.call (some (none,none)) function htrRequestListArguments) .skip

def htrRequestListStep : ProgHOL 64 :=
  .seq (htrRequestListBranch 0 (ofString "htr_deposit"))
    (.seq (htrRequestListBranch 1 (ofString "htr_wdreq"))
      (.seq (htrRequestListBranch 2 (ofString "htr_cons"))
        (.seq (htrRequestListBranch 3 (ofString "htr_bdep"))
          (.seq (htrRequestListBranch 4 (ofString "htr_bexit"))
            (.assign .local (ofString "i") (.op .add [.var .local (ofString "i"),.const 1]))))))

def htrRequestListCondition : ExpHOL 64 := .cmp .less (.var .local (ofString "i")) (.var .local (ofString "n"))

theorem source_htrRequestList_mark : htrRequestListAt 0 =
    .decCall (ofString "mark") .one (ofString "heap_mark") [] (htrRequestListAt 1) := by rfl

theorem source_htrRequestList_alloc : htrRequestListAt 1 =
    .decCall (ofString "roots") .one (ofString "alloc")
      [.op .add [.panop .mul [.var .local (ofString "n"),.const 32],.const 32]] (htrRequestListAt 2) := by rfl

theorem source_htrRequestList_zero : htrRequestListAt 2 =
    .dec (ofString "i") .one (.const 0) (htrRequestListAt 3) := by rfl

theorem source_htrRequestList_loop : htrRequestListAt 3 =
    .seq (.while htrRequestListCondition htrRequestListStep) (htrRequestListAt 4) := by rfl

theorem source_htrRequestList_hash : htrRequestListAt 4 =
    .seq (.call (some (none,none)) (ofString "htr_plist_chunks")
      [.var .local (ofString "roots"),.var .local (ofString "n"),.var .local (ofString "n"),.var .local (ofString "out")])
      (.seq (.call (some (none,none)) (ofString "heap_release") [.var .local (ofString "mark")]) (.return (.const 0))) := by rfl

#print axioms source_htrRequestList_mark
#print axioms source_htrRequestList_alloc
#print axioms source_htrRequestList_zero
#print axioms source_htrRequestList_loop
#print axioms source_htrRequestList_hash
end InitECandidate.Runtime
