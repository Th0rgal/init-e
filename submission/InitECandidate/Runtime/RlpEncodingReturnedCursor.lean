import InitECandidate.Runtime.EncWriters2GD
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000
/-- Extract the original scalar writer's real returned cursor and size. -/
theorem rlp_encode_word_returned_cursor {F : Type} (s post : PanSemStateFiniteExact 64 F)
 (dst input : BitVec 64) (value : ValueHOL 64) (DF : Nat)
 (code : s.code=originalRuntimeCode) (fence : Fence s.memaddrs DF) (cap : DF≤2^62)
 (dstLow : 8≤dst.toNat) (dstHigh : dst.toNat≤DF+8)
 (atDst : s.locals.lookup (ofString "dst")=some (.val (.word dst)))
 (atInput : s.locals.lookup (ofString "w")=some (.val (.word input)))
 (run : evaluateHOLFiniteState s (sourceFunctionBody Guest.guestFn_rlp_encode_word)=(some (.returned value),post)) :
 HdrRet DF dst value := by
 have spec:=encodeWord_win (D:=s.memaddrs) (B:=s.be) (A:=fun _=>True) (w:=0)
  fence (8#64) (by decide) (by decide) dst input dstLow (by omega)
 have dom : DomD s.memaddrs s.be s := ⟨(by intro address present;have bound:=fence address present;omega),rfl,rfl⟩
 have actual:=spec F s code dom trivial (by intro name impossible;exact False.elim impossible) s.globals rfl ⟨atDst,atInput⟩
 obtain ⟨globals,kept,result⟩:=actual.2.2.2.1 value (by rw [run])
 exact result

/-- Extract the actual byte encoder's returned cursor under the same domain
 fence. Byte sources may be unreadable; the premise is an actual successful return. -/
theorem rlp_encode_bytes_returned_cursor {F : Type} (s post : PanSemStateFiniteExact 64 F)
 (dst length : BitVec 64) (value : ValueHOL 64) (DF : Nat)
 (code : s.code=originalRuntimeCode) (fence : Fence s.memaddrs DF) (cap : DF≤2^62)
 (dstLow : 8≤dst.toNat) (dstHigh : dst.toNat≤DF+8)
 (atDst : s.locals.lookup (ofString "dst")=some (.val (.word dst)))
 (atLen : s.locals.lookup (ofString "n")=some (.val (.word length)))
 (run : evaluateHOLFiniteState s (sourceFunctionBody Guest.guestFn_rlp_encode_bytes)=(some (.returned value),post)) :
 WRet DF dst value := by
 have spec:=encodeBytes_win (D:=s.memaddrs) (B:=s.be) (A:=fun _=>True) (w:=0)
  fence cap (8#64) (by decide) (by decide) dst length dstLow (by omega)
 have dom : DomD s.memaddrs s.be s := ⟨(by intro address present;have bound:=fence address present;omega),rfl,rfl⟩
 have actual:=spec F s code dom trivial (by intro name impossible;exact False.elim impossible) s.globals rfl ⟨atDst,atLen⟩
 obtain ⟨globals,kept,result⟩:=actual.2.2.2.1 value (by rw [run])
 exact result
#print axioms rlp_encode_word_returned_cursor
#print axioms rlp_encode_bytes_returned_cursor
end InitECandidate.Runtime
