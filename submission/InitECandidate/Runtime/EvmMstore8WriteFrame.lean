import InitECandidate.Runtime.EvmMstore8Source
import InitECandidate.Runtime.InterpreterFundingByteStore
import InitECandidate.Runtime.AllocationFramedGlobals
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
/-- The actual MSTORE8 write is below the live-record frontier once its real
charged span has been established. It cannot wrap into live frame records. -/
theorem mstore8_write_returned_frame {F : Type}
 (s post : PanSemStateFiniteExact 64 F) (upper : Nat)
 (current : InterpreterFundingFrame) (ancestors : List InterpreterFundingFrame)
 (layout : InterpreterFundingLayout s current.address.toNat upper (current::ancestors))
 (base start scratch : BitVec 64) (a b c d : BitVec 64) (value : ValueHOL 64)
 (atFrame : s.globals.lookup (ofString "ev")=some (.val (.word current.address)))
 (domain : s.memaddrs (current.address+24))
 (baseAt : s.memory (current.address+24)=.word base)
 (startAt : s.locals.lookup (ofString "s")=some (.val (.word start)))
 (valueAt : s.locals.lookup (ofString "value")=some (fundingU256 a b c d))
 (extent : base.toNat+start.toNat+1≤scratch.toNat)
 (ordered : scratch.toNat≤current.address.toNat)
 (run : evaluateHOLFiniteState s (mstore8At 4)=(some (.returned value),post)) :
 ∃next,evaluateHOLFiniteState next (mstore8At 5)=(some (.returned value),post) ∧
 InterpreterFundingLayout next current.address.toNat upper (current::ancestors) ∧
 next.locals=s.locals ∧next.globals=s.globals ∧next.clock=s.clock ∧next.memaddrs=s.memaddrs ∧next.be=s.be ∧next.code=s.code ∧
 (∀watched : BitVec 64,scratch.toNat≤watched.toNat→next.memory watched=s.memory watched) := by
 let destination : ExpHOL 64:=.op .add [fundingLoad 24,.var .local (ofString "s")]
 let expression : ExpHOL 64:=.op .and [.rfield 0 (.var .local (ofString "value")),.const 255]
 have addressEval : @evalHOLExact 64 F _ s.toExact (fun a=>Classical.propDecidable (s.memaddrs a)) destination=some (.val (.word (base+start))) := by
  have load:=eval_fundingLoad s current.address (24#64) base atFrame domain baseAt
  simp [destination,evalHOLExact,evalListHOLExact,load,startAt,wordOpHOL,wordOp,valueIsWord,valueWord]
 have valueEval : @evalHOLExact 64 F _ s.toExact (fun a=>Classical.propDecidable (s.memaddrs a)) expression=some (.val (.word (a&&&255#64))) := by
  simp [expression,evalHOLExact,evalListHOLExact,valueAt,fundingU256,wordOpHOL,wordOp,valueIsWord,valueWord]
  change (a&&&(255#64&&&18446744073709551615#64))=a&&&255#64
  bv_decide
 have noReturn : ∀v,(evaluateHOLFiniteState s (.storeByte destination expression)).1≠some (.returned v) := by
  intro v
  rw [evaluateHOLFiniteState_storeByte,addressEval,valueEval]
  simp only [panMemStoreByteWord8HOL]
  split <;>simp
 rw [source_mstore8_4] at run
 obtain ⟨next,written,tail⟩:=seq_returned_of_nonreturning_first noReturn run
 have natural : (base+start).toNat=base.toNat+start.toNat:=BitVec.toNat_add_of_lt (by have h:=scratch.isLt;omega)
 have below : (base+start).toNat<current.address.toNat := by rw [natural];omega
 obtain ⟨funding,locals,globals,clock,domains,endian,code⟩:=interpreter_funding_store_byte_normal s next current.address.toNat upper (current::ancestors) layout destination expression (base+start) (a&&&255#64) below addressEval valueEval written
 refine ⟨next,tail,funding,locals,globals,clock,domains,endian,code,?_⟩
 obtain ⟨cell,equal⟩:=storeByte_normal s next destination expression (base+start) (a&&&255#64) addressEval valueEval written
 intro watched above
 rw [equal]
 apply sourceWriteByte_memory_other
 intro same
 have aligned : (panByteAlignHOL (base+start)).toNat≤(base+start).toNat := by rw [byteAlign_toNat];exact Nat.div_mul_le_self _ _
 have h:=congrArg BitVec.toNat same
 rw [natural] at aligned
 omega
#print axioms mstore8_write_returned_frame
end InitECandidate.Runtime
