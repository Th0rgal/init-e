import InitECandidate.Runtime.SourceCostLoopWorkP
namespace InitECandidate.Runtime.FineCost
open Flapjack

/-! Native-calibrated Loop prices, from root's checked `WordToStack` native caps
at the guest gap 6: conditional `I + T = 30 + 7`, loop iteration `2T + L = 16`,
call base 189 (handler push/pop, frame, liveness), 39 per spilled argument,
21 + 28 per returned word, continuation tick 7, and the leaf caps of
`loopWorkLeafCost` (an assignment priced by `loopNativeValue` of its
expression). `LoopWork` uses exactly these prices. -/

def nativeLoopPrice : LoopPrice := defaultLoopPrice

#print axioms nativeLoopPrice
end InitECandidate.Runtime.FineCost
