import InitECandidate.Runtime.EncodeHeaderPrefixPlan
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000
def EncodeHeaderCursorLower {F : Type} (s : PanSemStateFiniteExact 64 F) (floor : Nat) : Prop :=
 ∀dst : BitVec 64,s.locals.lookup (ofString "p")=some (.val (.word dst))→floor≤dst.toNat
/-- Successful actual writer/increment pairs never move p backwards. -/
theorem encode_header_writer_increment_lower {F : Type} (s middle next : PanSemStateFiniteExact 64 F)
 (writer : EncodeHeaderPrefixWriter) (input : ExpHOL 64)
 (header heap lo watched length : BitVec 64) (DF floor : Nat)
 (valid : EncodeHeaderPrefixInvariant s header heap lo watched length DF)
 (cap : DF≤2^62) (heapCap : heap.toNat≤33806089496) (heapFence : 33806089496≤DF)
 (aligned : lo.toNat%8=0) (below : watched.toNat<lo.toNat) (loHeap : lo.toNat≤heap.toNat)
 (callRun : evaluateHOLFiniteState s (encodeHeaderPrefixWriterCall writer input)=(none,middle))
 (incrementRun : evaluateHOLFiniteState middle encodeHeaderPrefixIncrement=(none,next))
 (lower : EncodeHeaderCursorLower s floor) : EncodeHeaderCursorLower next floor := by
 obtain ⟨cursor,atP,low,high⟩:=valid.cursor
 obtain ⟨written,fits,locals,_,_⟩:=encode_header_prefix_writer_normal s middle writer input cursor heap lo watched DF
  valid.code valid.fence cap heapCap heapFence aligned below loHeap low high atP valid.atHeap callRun
 have middleP : middle.locals.lookup (ofString "p")=some (.val (.word cursor)) := by
  rw [locals];simpa (config:={decide:=true}) [HolFiniteMapExact.lookup_update,FUPDATE] using atP
 have middleW : middle.locals.lookup (ofString "w")=some (.val (.word written)) := by
  rw [locals];simp [HolFiniteMapExact.lookup_update,FUPDATE]
 have increment:=encode_header_cursor_increment middle cursor written DF cap middleP middleW fits
 dsimp only [encodeHeaderPrefixIncrement] at incrementRun
 rw [increment.1] at incrementRun
 have equal:=(Prod.mk.inj incrementRun).2
 subst next
 intro dst atDst
 simp [setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE] at atDst
 subst dst
 have bound:=lower cursor atP
 rw [increment.2]
 omega
#print axioms encode_header_writer_increment_lower
end InitECandidate.Runtime
