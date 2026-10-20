import InitECandidate.Runtime.EncodeHeaderCursorLower
import InitECandidate.Runtime.EncodeHeaderReturnedPlan
import InitECandidate.Runtime.PanHandlerFreeCallControl
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000
theorem encode_header_seq_normal {F : Type} (s post : PanSemStateFiniteExact 64 F)
 (first tail : ProgHOL 64) (run : evaluateHOLFiniteState s (.seq first tail)=(none,post)) :
 ∃middle,evaluateHOLFiniteState s first=(none,middle) ∧evaluateHOLFiniteState middle tail=(none,post) := by
 rw [evaluateHOLFiniteState_seq_line780] at run
 cases firstRun : evaluateHOLFiniteState s first with
 | mk result middle=>
  rw [firstRun] at run
  cases result with
  | none=>exact ⟨middle,rfl,run⟩
  | some result=>simp at run

/-- A real returned finite writer plan reaches its actual tail with the bounded
cursor and original header cell intact; buf is retained by actual caller locals. -/
theorem encode_header_prefix_plan_normal {F : Type} (items : List (EncodeHeaderPrefixWriter×ExpHOL 64))
 (tail : ProgHOL 64) (s post : PanSemStateFiniteExact 64 F)  (header heap lo watched length : BitVec 64) (DF : Nat)
 (valid : EncodeHeaderPrefixInvariant s header heap lo watched length DF)
 (cap : DF≤2^62) (heapCap : heap.toNat≤33806089496) (heapFence : 33806089496≤DF)
 (aligned : lo.toNat%8=0) (below : watched.toNat<lo.toNat) (loHeap : lo.toNat≤heap.toNat)
 (run : evaluateHOLFiniteState s (encodeHeaderPrefixPlan items tail)=(none,post)) :
 ∃next,evaluateHOLFiniteState next tail=(none,post) ∧
 EncodeHeaderPrefixInvariant next header heap lo watched length DF ∧
 next.locals.lookup (ofString "buf")=s.locals.lookup (ofString "buf") ∧
 (∀floor,EncodeHeaderCursorLower s floor→EncodeHeaderCursorLower next floor) := by
 induction items generalizing s with
 | nil=>exact ⟨s,run,valid,rfl,fun _ lower=>lower⟩
 | cons item rest ih=>
  obtain ⟨middle,firstRun,tailRun⟩:=encode_header_seq_normal s post _ _ run
  obtain ⟨dst,written,increment,nextValid⟩:=encode_header_prefix_writer_advance s middle item.1 item.2
   header heap lo watched length DF valid cap heapCap heapFence aligned below loHeap firstRun
  change evaluateHOLFiniteState middle (.seq encodeHeaderPrefixIncrement (encodeHeaderPrefixPlan rest tail))=_ at tailRun
  rw [evaluateHOLFiniteState_seq_line780] at tailRun
  dsimp only [encodeHeaderPrefixIncrement] at tailRun
  rw [increment] at tailRun
  obtain ⟨next,returned,kept,buf,moves⟩:=ih _ nextValid tailRun
  have moved : ∀floor,EncodeHeaderCursorLower s floor→EncodeHeaderCursorLower
    (setVarHOLFinite (ofString "p") (.val (.word (dst+written))) middle) floor := by
   intro floor lower
   exact encode_header_writer_increment_lower s middle _ item.1 item.2 header heap lo watched length DF floor
    valid cap heapCap heapFence aligned below loHeap firstRun increment lower
  refine ⟨next,returned,kept,buf.trans ?_,fun floor lower=>moves floor (moved floor lower)⟩
  obtain ⟨cursor,atP,low,high⟩:=valid.cursor
  obtain ⟨advance,_,locals,_,_⟩:=encode_header_prefix_writer_normal s middle item.1 item.2 cursor heap lo watched DF
   valid.code valid.fence cap heapCap heapFence aligned below loHeap low high atP valid.atHeap firstRun
  change (middle.locals.update (ofString "p",.val (.word (dst+written)))).lookup (ofString "buf")=_
  rw [locals]
  simp (config:={decide:=true}) [HolFiniteMapExact.lookup_update,FUPDATE]
/-- A last actual writer/increment pair also preserves the cursor envelope. -/
theorem encode_header_writer_pair_normal {F : Type} (s post : PanSemStateFiniteExact 64 F)
 (writer : EncodeHeaderPrefixWriter) (input : ExpHOL 64)
 (header heap lo watched length : BitVec 64) (DF : Nat)
 (valid : EncodeHeaderPrefixInvariant s header heap lo watched length DF)
 (cap : DF≤2^62) (heapCap : heap.toNat≤33806089496) (heapFence : 33806089496≤DF)
 (aligned : lo.toNat%8=0) (below : watched.toNat<lo.toNat) (loHeap : lo.toNat≤heap.toNat)
 (run : evaluateHOLFiniteState s (.seq (encodeHeaderPrefixWriterCall writer input) encodeHeaderPrefixIncrement)=(none,post)) :
 EncodeHeaderPrefixInvariant post header heap lo watched length DF ∧
 post.locals.lookup (ofString "buf")=s.locals.lookup (ofString "buf") ∧
 (∀floor,EncodeHeaderCursorLower s floor→EncodeHeaderCursorLower post floor) := by
 obtain ⟨middle,firstRun,incrementRun⟩:=encode_header_seq_normal s post _ _ run
 obtain ⟨dst,written,increment,nextValid⟩:=encode_header_prefix_writer_advance s middle writer input
  header heap lo watched length DF valid cap heapCap heapFence aligned below loHeap firstRun
 have moved:=fun floor lower=>encode_header_writer_increment_lower s middle post writer input
  header heap lo watched length DF floor valid cap heapCap heapFence aligned below loHeap firstRun incrementRun lower
 dsimp only [encodeHeaderPrefixIncrement] at incrementRun
 rw [increment] at incrementRun
 have equal:=(Prod.mk.inj incrementRun).2
 subst post
 refine ⟨nextValid,?_,moved⟩
 obtain ⟨cursor,atP,low,high⟩:=valid.cursor
 obtain ⟨advance,_,locals,_,_⟩:=encode_header_prefix_writer_normal s middle writer input cursor heap lo watched DF
  valid.code valid.fence cap heapCap heapFence aligned below loHeap low high atP valid.atHeap firstRun
 change (middle.locals.update (ofString "p",.val (.word (dst+written)))).lookup (ofString "buf")=_
 rw [locals]
 simp (config:={decide:=true}) [HolFiniteMapExact.lookup_update,FUPDATE]
#print axioms encode_header_writer_pair_normal
#print axioms encode_header_seq_normal
#print axioms encode_header_prefix_plan_normal
end InitECandidate.Runtime
