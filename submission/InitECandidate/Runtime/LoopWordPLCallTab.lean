import InitECandidate.Runtime.LoopWordPLSiteCert
import InitECandidate.Runtime.CallSiteTable
import InitECandidate.Runtime.LoopWordPLInstance
import InitECandidate.Runtime.WordSimpTab
namespace InitECandidate.Runtime.FineCost
open Flapjack

/-! The WordSimp site charge and the caller+callee envelope charge (table data
in `CallSiteTable`). -/

/-- The WordSimp site charge at a return label (as in `wsLoopPrice`). -/
def siteA (l : Nat × Nat) (_ : Option Nat) : Nat :=
  24 * (tLookup wsT2 (0, l.1, [l.2]) + tLookup wsT1 (0, l.1, [l.2]))

/-- The caller+callee envelope charge. -/
def siteB (l : Nat × Nat) (t : Option Nat) : Nat := 24 * callTabGet (l.1, t)

theorem siteA_eq (c : Compiler.Encoders.Asm.AsmConfigExact 64) : (wsLoopPrice c wsT1 wsT2).site = siteA := rfl

#print axioms siteA_eq

end InitECandidate.Runtime.FineCost
