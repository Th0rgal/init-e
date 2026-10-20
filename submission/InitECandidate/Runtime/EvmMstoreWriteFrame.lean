import InitECandidate.Runtime.EvmMstoreSource
import InitECandidate.Runtime.U256StoreDiscardUpperFrame
import InitECandidate.Runtime.AllocationFramedGlobals
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
/-- Actual MSTORE word-writer call, protected by its same charged32-byte span. -/
theorem mstore_write_returned_frame {F : Type}
 (s post : PanSemStateFiniteExact 64 F) (upper : Nat)
 (current : InterpreterFundingFrame) (ancestors : List InterpreterFundingFrame)
 (layout : InterpreterFundingLayout s current.address.toNat upper (current::ancestors))
 (base start scratch : BitVec 64) (a b c d : BitVec 64) (value : ValueHOL 64)
 (atFrame : s.globals.lookup (ofString "ev")=some (.val (.word current.address)))
 (domain : s.memaddrs (current.address+24))
 (baseAt : s.memory (current.address+24)=.word base)
 (startAt : s.locals.lookup (ofString "s")=some (.val (.word start)))
 (valueAt : s.locals.lookup (ofString "value")=some (fundingU256 a b c d))
 (extent : base.toNat+start.toNat+32≤scratch.toNat)
 (ordered : scratch.toNat≤current.address.toNat)
 (code : s.code=originalRuntimeCode) (domOK : DomOK s.memaddrs)
 (run : evaluateHOLFiniteState s (mstoreAt 4)=(some (.returned value),post)) :
 ∃next,evaluateHOLFiniteState next (mstoreAt 5)=(some (.returned value),post) ∧
 InterpreterFundingLayout next current.address.toNat upper (current::ancestors) ∧
 next.locals=s.locals ∧next.globals=s.globals ∧next.memaddrs=s.memaddrs ∧next.be=s.be ∧next.code=s.code ∧
 (∀watched : BitVec 64,scratch.toNat≤watched.toNat→next.memory watched=s.memory watched) := by
 let arguments : List (ExpHOL 64):=[.var .local (ofString "value"),.op .add [fundingLoad 24,.var .local (ofString "s")]]
 have load:=eval_fundingLoad s current.address (24#64) base atFrame domain baseAt
 have args : evalListHOLFinite s (h:=fun x=>Classical.propDecidable (s.memaddrs x)) arguments=some [fundingU256 a b c d,.val (.word (base+start))] := by
  simp [arguments,evalListHOLFinite,evalListHOLExact,evalHOLExact,load,startAt,valueAt,wordOpHOL,wordOp,valueIsWord,valueWord]
 rw [source_mstore_4] at run
 obtain ⟨next,written,tail⟩:=seq_returned_of_nonreturning_first (fun v=>discard_call_not_returned s (ofString "u256_to_be32") arguments v) run
 have natural : (base+start).toNat=base.toNat+start.toNat:=BitVec.toNat_add_of_lt (by have h:=scratch.isLt;omega)
 have writerExtent : (base+start).toNat+32≤scratch.toNat := by rw [natural];exact extent
 have within : scratch.toNat≤2^64 := by have h:=scratch.isLt;omega
 have keptUpper (watched : BitVec 64) (above : scratch.toNat≤watched.toNat) :=u256_store_discard_normal_upper s next arguments a b c d (base+start) watched scratch.toNat args writerExtent within above code domOK written
 have metadata:=evaluateHOLFiniteState_metadata s (.call (some (none,none)) (ofString "u256_to_be32") arguments)
 rw [written] at metadata
 obtain ⟨_,globals,locals⟩:=keptUpper current.address ordered
 refine ⟨next,tail,?_,locals,globals,metadata.2.1,metadata.2.2.1,metadata.1,fun watched above=>(keptUpper watched above).1⟩
 constructor
 · exact layout.upperBound
 · intro record member
   have valid:=layout.records record member
   apply InterpreterFundingFrameAt.after_frame (post:=next) valid metadata.2.1
   intro offset included
   have small : offset.toNat<280 := by
    simp only [interpreterFundingOffsets,List.mem_cons,List.not_mem_nil,or_false] at included
    rcases included with rfl|rfl|rfl|rfl <;>decide
   have natural:=interpreter_funding_offset_natural record upper valid.extent layout.upperBound offset small
   exact (keptUpper (record.address+offset) (by rw [natural];have low:=valid.lowerBound;omega)).1
 · exact layout.disjoint
 · exact layout.budget
#print axioms mstore_write_returned_frame
end InitECandidate.Runtime
