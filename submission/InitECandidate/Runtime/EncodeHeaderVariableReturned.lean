import InitECandidate.Runtime.EncodeHeaderReturnedPlan
import InitECandidate.Runtime.EncodeHeaderVariableBytesBound
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000
private def variableCall : ProgHOL 64 := .call (some (some (.local,ofString "w"),none)) (ofString "rlp_encode_bytes")
 [.var .local (ofString "p"),encodeHeaderPrefixField 128,encodeHeaderPrefixField 136]
/-- A normal real variable call equals the literal call at the retained word;
inaccessible length loads cannot normally complete. -/
theorem encode_header_variable_call_normal {F : Type} (s middle : PanSemStateFiniteExact 64 F)
 (header heap lo length : BitVec 64) (DF : Nat)
 (valid : EncodeHeaderPrefixInvariant s header heap lo (header+136) length DF)
 (run : evaluateHOLFiniteState s variableCall=(none,middle)) :
 evaluateHOLFiniteState s (encodeHeaderPrefixWriterCall (.bytes length) (encodeHeaderPrefixField 128))=(none,middle) := by
 by_cases readable : s.memaddrs (header+136)
 · have loaded : @evalHOLExact 64 F _ s.toExact (fun a=>Classical.propDecidable (s.memaddrs a))
    (encodeHeaderPrefixField 136)=some (.val (.word length)) := by
    simp [encodeHeaderPrefixField,evalHOLExact,evalListHOLExact,valid.atH,wordOpHOL,wordOp,
     valueIsWord,valueWord,isWfShapeExactHOL,memLoadHOLExact]
    exact ⟨readable,valid.atLength⟩
   have same : evalListHOLFinite s (h:=fun a=>Classical.propDecidable (s.memaddrs a))
     [.var .local (ofString "p"),encodeHeaderPrefixField 128,encodeHeaderPrefixField 136]=
    evalListHOLFinite s (h:=fun a=>Classical.propDecidable (s.memaddrs a))
     [.var .local (ofString "p"),encodeHeaderPrefixField 128,.const length] := by
    simp only [evalListHOLFinite_eq_toExact,evalListHOLExact,loaded,evalHOLExact]
   simpa only [variableCall,encodeHeaderPrefixWriterCall,evaluateHOLFiniteState_call,same] using run
 · have failed : @evalHOLExact 64 F _ s.toExact (fun a=>Classical.propDecidable (s.memaddrs a))
    (encodeHeaderPrefixField 136)=none := by
    simp [encodeHeaderPrefixField,evalHOLExact,evalListHOLExact,valid.atH,wordOpHOL,wordOp,
     valueIsWord,valueWord,isWfShapeExactHOL,memLoadHOLExact]
    exact readable
   have args : evalListHOLFinite s (h:=fun a=>Classical.propDecidable (s.memaddrs a))
     [.var .local (ofString "p"),encodeHeaderPrefixField 128,encodeHeaderPrefixField 136]=none := by
    rw [evalListHOLFinite_eq_toExact]
    cases firstEval : @evalHOLExact 64 F _ s.toExact (fun a=>Classical.propDecidable (s.memaddrs a)) (.var .local (ofString "p")) <;>
     cases secondEval : @evalHOLExact 64 F _ s.toExact (fun a=>Classical.propDecidable (s.memaddrs a)) (encodeHeaderPrefixField 128) <;>
     simp only [evalListHOLExact,failed,firstEval,secondEval]
   simp only [variableCall,evaluateHOLFiniteState_call,args] at run
   simp at run

/-- The actual variable field and following increment retain the header cursor. -/
theorem encode_header_variable_returned {F : Type} (s post : PanSemStateFiniteExact 64 F) (value : ValueHOL 64)
 (header heap lo length : BitVec 64) (DF : Nat)
 (valid : EncodeHeaderPrefixInvariant s header heap lo (header+136) length DF)
 (cap : DF≤2^62) (heapCap : heap.toNat≤33806089496) (heapFence : 33806089496≤DF)
 (aligned : lo.toNat%8=0) (below : (header+136).toNat<lo.toNat) (loHeap : lo.toNat≤heap.toNat)
 (run : evaluateHOLFiniteState s (encodeHeaderAt 26)=(some (.returned value),post)) :
 ∃next,evaluateHOLFiniteState next (encodeHeaderAt 28)=(some (.returned value),post) ∧
 EncodeHeaderPrefixInvariant next header heap lo (header+136) length DF ∧
 next.locals.lookup (ofString "buf")=s.locals.lookup (ofString "buf") ∧
 (∀floor,EncodeHeaderCursorLower s floor→EncodeHeaderCursorLower next floor) := by
 have stage : encodeHeaderAt 26=.seq variableCall (encodeHeaderAt 27) := rfl
 rw [stage] at run
 obtain ⟨middle,callRun,tailRun⟩:=encode_header_seq_returned_of_no_return s post _ _ value
  ((evaluate_handlerFree_call_control s _ _ _).2.2) run
 have literalRun:=encode_header_variable_call_normal s middle header heap lo length DF valid callRun
 obtain ⟨dst,written,increment,nextValid⟩:=encode_header_prefix_writer_advance s middle (.bytes length) (encodeHeaderPrefixField 128)
  header heap lo (header+136) length DF valid cap heapCap heapFence aligned below loHeap literalRun
 have stage27 : encodeHeaderAt 27=.seq encodeHeaderPrefixIncrement (encodeHeaderAt 28) := rfl
 rw [stage27,evaluateHOLFiniteState_seq_line780] at tailRun
 dsimp only [encodeHeaderPrefixIncrement] at tailRun
 rw [increment] at tailRun
 have moved : ∀floor,EncodeHeaderCursorLower s floor→EncodeHeaderCursorLower
   (setVarHOLFinite (ofString "p") (.val (.word (dst+written))) middle) floor := by
  intro floor lower
  exact encode_header_writer_increment_lower s middle _ (.bytes length) (encodeHeaderPrefixField 128)
   header heap lo (header+136) length DF floor valid cap heapCap heapFence aligned below loHeap literalRun increment lower
 refine ⟨_,tailRun,nextValid,?_,moved⟩
 obtain ⟨cursor,atP,low,high⟩:=valid.cursor
 obtain ⟨advance,_,locals,_,_⟩:=encode_header_bytes_assignment_frame s middle (encodeHeaderPrefixField 128) cursor length lo (header+136) DF
  valid.code valid.fence cap aligned below low high atP literalRun
 change (middle.locals.update (ofString "p",.val (.word (dst+written)))).lookup (ofString "buf")=_
 rw [locals]
 simp (config:={decide:=true}) [HolFiniteMapExact.lookup_update,FUPDATE]
#print axioms encode_header_variable_call_normal
#print axioms encode_header_variable_returned
end InitECandidate.Runtime
