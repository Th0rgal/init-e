import InitECandidate.Runtime.OriginalDecodeRequestsCode
import InitECandidate.Runtime.SszSplitVarListSource
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

def reqGlobal : ExpHOL 64 := .var .global (ofString "ssz_offs")

def reqLoopBody : ProgHOL 64 :=
  .seq (.store (.op .add [reqGlobal, .panop .mul [sszLocal "i", .const 8]]) sszSplitOffsetAt)
    (.assign .local (ofString "i") (.op .add [sszLocal "i", .const 1]))

def reqLoop : ProgHOL 64 := .while (.cmp .less (sszLocal "i") (.const 5)) reqLoopBody

def reqCheck : ProgHOL 64 :=
  .call (some (none,none)) (ofString "ssz_check_offsets") [reqGlobal, .const 5, .const 20, sszLocal "len"]

def reqStore (offset : BitVec 64) (value : ExpHOL 64) (rest : ProgHOL 64) : ProgHOL 64 :=
  .seq (.store (.op .add [sszLocal "rq", .const offset]) value) rest

def reqStores : ProgHOL 64 :=
  reqStore 0 (.op .add [sszLocal "p", sszLocal "o0"]) (reqStore 8 (sszLocal "n0")
  (reqStore 16 (.op .add [sszLocal "p", sszLocal "o1"]) (reqStore 24 (sszLocal "n1")
  (reqStore 32 (.op .add [sszLocal "p", sszLocal "o2"]) (reqStore 40 (sszLocal "n2")
  (reqStore 48 (.op .add [sszLocal "p", sszLocal "o3"]) (reqStore 56 (sszLocal "n3")
  (reqStore 64 (.op .add [sszLocal "p", sszLocal "o4"]) (reqStore 72 (sszLocal "n4")
  (.return (sszLocal "rq")))))))))))

def reqCount (n a b : String) (size : BitVec 64) (rest : ProgHOL 64) : ProgHOL 64 :=
  .decCall (ofString n) .one (ofString "ssz_fixed_list_count")
    [.op .sub [sszLocal a, sszLocal b], .const size, .const 9223372036854775807] rest

def reqCounts : ProgHOL 64 :=
  reqCount "n0" "o1" "o0" 192 (reqCount "n1" "o2" "o1" 76 (reqCount "n2" "o3" "o2" 116
    (reqCount "n3" "o4" "o3" 184 (reqCount "n4" "len" "o4" 68 reqStores))))

def reqLoadAt (offset : BitVec 64) : ExpHOL 64 := .load .one (.op .add [reqGlobal, .const offset])

def reqLoads : ProgHOL 64 :=
  .dec (ofString "o0") .one (.load .one reqGlobal) (.dec (ofString "o1") .one (reqLoadAt 8)
    (.dec (ofString "o2") .one (reqLoadAt 16) (.dec (ofString "o3") .one (reqLoadAt 24)
      (.dec (ofString "o4") .one (reqLoadAt 32) reqCounts))))

def reqAlloc : ProgHOL 64 := .decCall (ofString "rq") .one (ofString "alloc") [.const 80] reqLoads

def reqAfterLen : ProgHOL 64 := .dec (ofString "i") .one (.const 0) (.seq reqLoop (.seq reqCheck reqAlloc))

theorem source_decodeRequests_body : sourceFunctionBody Guest.guestFn_decode_requests =
    .seq (.ite (.cmp .lower (sszLocal "len") (.const 20)) (.call (some (none,none)) (ofString "ssz_fail") [.const 60]) .skip)
      reqAfterLen := by cbv

#print axioms source_decodeRequests_body
end InitECandidate.Runtime
