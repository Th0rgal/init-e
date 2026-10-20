import InitECandidate.Runtime.RlpLongTailDecCall
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

/-- **The actual long-header tail of `rlp_write_header`.**  It reads the byte count from the real
`rlp_be_len` call (which writes no memory and returns a word of at most eight bytes), stores the
length byte at `dst`, writes the count at `dst + 1` through the real `rlp_put_be`, and returns the
total length.  Every word outside the nine-byte window at `dst` keeps its cell. -/
theorem rlpWriteHeaderTail_window {F : Type} (s : PanSemStateFiniteExact 64 F)
    (D N B0 w : BitVec 64) (out : ¬ MWin D 9 w)
    (hd : s.locals.lookup (ofString "dst") = some (.val (.word D)))
    (hn : s.locals.lookup (ofString "n") = some (.val (.word N)))
    (hb : s.locals.lookup (ofString "base") = some (.val (.word B0)))
    (code : s.code = originalRuntimeCode) :
    (evaluateHOLFiniteState s rlpWriteHeaderTail).2.memory w = s.memory w := by
  rw [rlpWriteHeaderTail]
  exact rlpLongTailDecCall_window s D N w out
    (.op .add [.var .local (ofString "base"), .const (55#64), .var .local (ofString "ll")])
    (ofString "n") (by decide) hd hn code

#print axioms rlpWriteHeaderTail_window

end InitECandidate.Runtime
