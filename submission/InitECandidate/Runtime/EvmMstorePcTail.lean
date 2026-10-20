import InitECandidate.Runtime.EvmMstoreSource
import InitECandidate.Runtime.EvmMstore8PcTail
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
set_option maxRecDepth 100000
theorem mstore_pc_tail_returned_funding {F : Type}
 (s post : PanSemStateFiniteExact 64 F) (upper : Nat)
 (current : InterpreterFundingFrame) (ancestors : List InterpreterFundingFrame)
 (layout : InterpreterFundingLayout s current.address.toNat upper (current::ancestors))
 (pc : BitVec 64) (value : ValueHOL 64)
 (atFrame : s.globals.lookup (ofString "ev")=some (.val (.word current.address)))
 (domain : s.memaddrs (current.address+0))
 (pcAt : s.memory (current.address+0)=.word pc)
 (code : s.code=originalRuntimeCode)
 (run : evaluateHOLFiniteState s (mstoreAt 5)=(some (.returned value),post)) :
 value=.val (.word 0) ∧InterpreterFundingLayout post current.address.toNat upper (current::ancestors) ∧
 post.memory=(sourceWriteWord s (current.address+0) (pc+1)).memory ∧post.globals=s.globals ∧post.memaddrs=s.memaddrs ∧post.be=s.be ∧post.code=s.code := by
 have identical : mstoreAt 5=mstore8At 5:=rfl
 rw [identical] at run
 exact mstore8_pc_tail_returned_funding s post upper current ancestors layout pc value atFrame domain pcAt code run
#print axioms mstore_pc_tail_returned_funding
end InitECandidate.Runtime
