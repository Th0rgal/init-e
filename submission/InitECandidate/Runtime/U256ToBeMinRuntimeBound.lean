import InitECandidate.Runtime.BlockRlpLengthLoopDeclaration
import InitECandidate.Runtime.EncToBeMinGD
import InitECandidate.Runtime.OriginalEncodeCode
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000
def u256ToBeMinLoopBody : ProgHOL 64 :=
 match tbBody with
 | .decCall _ _ _ _ (.dec _ _ _ (.seq (.while _ body) _))=>body
 | _=>.skip
def u256ToBeMinPosition : ExpHOL 64 :=
 match u256ToBeMinLoopBody with
 | .dec _ _ value _=>value
 | _=>.const 0
def u256ToBeMinLimbArguments : List (ExpHOL 64) :=
 match u256ToBeMinLoopBody with
 | .dec _ _ _ (.decCall _ _ _ args _)=>args
 | _=>[]
def u256ToBeMinByteStore : ProgHOL 64 :=
 match u256ToBeMinLoopBody with
 | .dec _ _ _ (.decCall _ _ _ _ (.seq store _))=>store
 | _=>.skip

theorem source_u256_to_be_min_loop : u256ToBeMinLoopBody=
 .dec (ofString "pos") .one u256ToBeMinPosition
  (.decCall (ofString "l") .one (ofString "u256_limb") u256ToBeMinLimbArguments
   (.seq u256ToBeMinByteStore (.assign .local (ofString "i") (.op .add [.var .local (ofString "i"),.const 1])))) := rfl

theorem u256_to_be_min_loop_counted : BlockRlpCountedBody (ofString "i") u256ToBeMinLoopBody 1 := by
 rw [source_u256_to_be_min_loop]
 refine ⟨?_,by decide_cbv,?_⟩
 · have tail : ProgBounded (.seq u256ToBeMinByteStore (.assign .local (ofString "i") (.op .add [.var .local (ofString "i"),.const 1]))) 0 := ProgBounded.straight _ (by decide_cbv)
   have call : ProgBounded (.decCall (ofString "l") .one (ofString "u256_limb") u256ToBeMinLimbArguments
    (.seq u256ToBeMinByteStore (.assign .local (ofString "i") (.op .add [.var .local (ofString "i"),.const 1])))) (0+1+0) :=
    ProgBounded.decCall vmBound_u256_limb _ _ _ tail
   intro F state code budget
   exact ProgBounded.dec (ofString "pos") .one u256ToBeMinPosition call state code budget
 · exact block_rlp_counter_dec _ _ _ _ _ (by decide)
    (block_rlp_counter_decCall _ _ _ _ _ _ (by decide)
     (block_rlp_counter_seq _ _ _ (by decide_cbv) (block_rlp_counter_incr _)))

def u256ToBeMinSourceCost : Nat := 6+2*(2^64-1)
/-- Complete original minimal big-endian writer. No returned-length, input
shape, readable-memory, destination geometry or successful-store premise. -/
theorem u256_to_be_min_body_bounded : ProgBounded (sourceFunctionBody Guest.guestFn_u256_to_be_min) u256ToBeMinSourceCost := by
 have rest : ProgBounded (.return (.var .local (ofString "len"))) 0 := ProgBounded.straight _ rfl
 have loop : ProgBounded (.dec (ofString "i") .one (.const 0)
  (.seq (.while (.cmp .lower (.var .local (ofString "i")) (.var .local (ofString "len"))) u256ToBeMinLoopBody)
   (.return (.var .local (ofString "len"))))) ((2^64-1)*(1+1)+0) :=
  ProgBounded.blockRlpCountedDec (ofString "i") (ofString "len") .lower (Or.inr rfl)
   u256_to_be_min_loop_counted (by decide_cbv) rest
 have bounded : ProgBounded tbBody (5+1+((2^64-1)*(1+1)+0)) :=
  ProgBounded.decCall vmBound_u256_byte_length (ofString "len") .one [.var .local (ofString "a")] loop
 intro F state code budget
 rw [tbBody_eq]
 have result:=bounded state code (by simpa [u256ToBeMinSourceCost,Nat.mul_comm] using budget)
 simpa [u256ToBeMinSourceCost,Nat.mul_comm] using result
theorem u256_to_be_min_fun_bounded : FunBounded (ofString "u256_to_be_min") u256ToBeMinSourceCost :=
 ⟨_,_,_,originalRuntimeCode_u256ToBeMin_lookup,u256_to_be_min_body_bounded⟩
#print axioms u256_to_be_min_loop_counted
#print axioms u256_to_be_min_body_bounded
#print axioms u256_to_be_min_fun_bounded
end InitECandidate.Runtime
