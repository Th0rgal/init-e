import InitECandidate.Runtime.EncodeHeaderVariableReturned
import InitECandidate.Runtime.EncodeHeaderNormalPlan
import InitECandidate.Runtime.NoDirectReturn
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000
private def tailInput (index : Nat) : ExpHOL 64 := match encodeHeaderAt index with
 | .seq (.call _ _ args) _=>args[1]?.getD (.const 0)
 | _=>.const 0
private def fixedItems : List (EncodeHeaderPrefixWriter×ExpHOL 64) :=
 [(.bytes 32,tailInput 28),(.bytes 8,tailInput 30),(.u256,tailInput 32),
  (.bytes 32,tailInput 34),(.word,tailInput 36),(.word,tailInput 38),
  (.bytes 32,tailInput 40),(.bytes 32,tailInput 42)]
private def forkProgram : ProgHOL 64 := match encodeHeaderAt 44 with | .seq first _=>first | _=>.skip
private def forkYes : ProgHOL 64 := match forkProgram with | .ite _ yes _=>yes | _=>.skip
private def forkNo : ProgHOL 64 := match forkProgram with | .ite _ _ no=>no | _=>.skip
private def forkCondition : ExpHOL 64 := match forkProgram with | .ite c _ _=>c | _=>.const 0
private def forkInput (index : Nat) : ExpHOL 64 := match (statelessNext^[index]) forkYes with
 | .seq (.call _ _ args) _=>args[1]?.getD (.const 0)
 | _=>.const 0
private def forkItems : List (EncodeHeaderPrefixWriter×ExpHOL 64) :=
 [(.bytes 32,forkInput 0)]
theorem encode_header_fixed_returned {F : Type} (s post : PanSemStateFiniteExact 64 F) (value : ValueHOL 64)
 (header heap lo length : BitVec 64) (DF : Nat)
 (valid : EncodeHeaderPrefixInvariant s header heap lo (header+136) length DF)
 (cap : DF≤2^62) (heapCap : heap.toNat≤33806089496) (heapFence : 33806089496≤DF)
 (aligned : lo.toNat%8=0) (below : (header+136).toNat<lo.toNat) (loHeap : lo.toNat≤heap.toNat)
 (run : evaluateHOLFiniteState s (encodeHeaderAt 28)=(some (.returned value),post)) :
 ∃next,evaluateHOLFiniteState next (encodeHeaderAt 45)=(some (.returned value),post) ∧
 EncodeHeaderPrefixInvariant next header heap lo (header+136) length DF ∧
 next.locals.lookup (ofString "buf")=s.locals.lookup (ofString "buf") ∧
 (∀floor,EncodeHeaderCursorLower s floor→EncodeHeaderCursorLower next floor) := by
 have source28 : encodeHeaderAt 28=encodeHeaderPrefixPlan fixedItems (encodeHeaderAt 44) := rfl
 rw [source28] at run
 obtain ⟨forkState,forkRun,forkValid,forkBuf,forkMoves⟩:=encode_header_prefix_plan_returned fixedItems (encodeHeaderAt 44) s post value
  header heap lo (header+136) length DF valid cap heapCap heapFence aligned below loHeap run
 have source44 : encodeHeaderAt 44=.seq forkProgram (encodeHeaderAt 45) := rfl
 rw [source44] at forkRun
 obtain ⟨next,normal,returned⟩:=encode_header_seq_returned_of_no_return forkState post _ _ value
  (fun v=>evaluate_noDirectReturn forkProgram (by decide_cbv) forkState v) forkRun
 have branches : evaluateHOLFiniteState forkState forkNo=(none,next) ∨
  evaluateHOLFiniteState forkState forkYes=(none,next) := by
  have sourceFork : forkProgram=.ite forkCondition forkYes forkNo := rfl
  rw [sourceFork,evaluateHOLFiniteState_ite] at normal
  split at normal
  · split at normal
    · exact Or.inl normal
    · exact Or.inr normal
  · simp at normal
 rcases branches with noRun|yesRun
 · have sourceNo : forkNo=.skip := rfl
   rw [sourceNo,evaluateHOLFiniteState_skip] at noRun
   have same:=(Prod.mk.inj noRun).2
   subst next
   exact ⟨forkState,returned,forkValid,forkBuf,forkMoves⟩
 · have sourceYes : forkYes=encodeHeaderPrefixPlan forkItems
    (.seq (encodeHeaderPrefixWriterCall .word (forkInput 2)) encodeHeaderPrefixIncrement) := rfl
   rw [sourceYes] at yesRun
   obtain ⟨finished,lastRun,finishedValid,finishedBuf,finishedMoves⟩:=encode_header_prefix_plan_normal forkItems
    (.seq (encodeHeaderPrefixWriterCall .word (forkInput 2)) encodeHeaderPrefixIncrement) forkState next
    header heap lo (header+136) length DF forkValid cap heapCap heapFence aligned below loHeap yesRun
   obtain ⟨nextValid,nextBuf,nextMoves⟩:=encode_header_writer_pair_normal finished next .word (forkInput 2)
    header heap lo (header+136) length DF finishedValid cap heapCap heapFence aligned below loHeap lastRun
   exact ⟨next,returned,nextValid,nextBuf.trans (finishedBuf.trans forkBuf),
    fun floor lower=>nextMoves floor (finishedMoves floor (forkMoves floor lower))⟩
#print axioms encode_header_fixed_returned
end InitECandidate.Runtime
