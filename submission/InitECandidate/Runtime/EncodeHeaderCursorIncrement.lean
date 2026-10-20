import InitECandidate.Runtime.EncodeHeaderU256AssignmentFrame
import InitECandidate.Runtime.CountedLoop
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000
/-- The real cursor update after a writer is a natural (nonwrapping) advance. -/
theorem encode_header_cursor_increment {F : Type} (s : PanSemStateFiniteExact 64 F)
 (dst written : BitVec 64) (DF : Nat) (cap : DF≤2^62)
 (atP : s.locals.lookup (ofString "p")=some (.val (.word dst)))
 (atW : s.locals.lookup (ofString "w")=some (.val (.word written)))
 (fits : dst.toNat+written.toNat≤DF+8) :
 evaluateHOLFiniteState s (.assign .local (ofString "p")
  (.op .add [.var .local (ofString "p"),.var .local (ofString "w")]))=
  (none,setVarHOLFinite (ofString "p") (.val (.word (dst+written))) s) ∧
 (dst+written).toNat=dst.toNat+written.toNat := by
 constructor
 · simp [evaluateHOLFiniteState_assign,evalHOLExact,evalListHOLExact,atP,atW,wordOpHOL,wordOp,valueIsWord,
    valueWord,lookupKvarHOLExact,isValidValueHOLExact,setKvarHOLFinite,shapeOfHOLExact,shapeEqHOL]
 · rw [BitVec.toNat_add, Nat.mod_eq_of_lt]
   omega
#print axioms encode_header_cursor_increment
end InitECandidate.Runtime
