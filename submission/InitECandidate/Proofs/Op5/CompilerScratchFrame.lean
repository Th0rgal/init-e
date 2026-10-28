import InitECandidate.Proofs.Op5.FrameBridge

namespace InitE.Op5
open Flapjack
open Flapjack.Compiler.Encoders.Asm

/-- Re-export of the two-region `WordToStack` and target code/stack frame bridges. -/
theorem compilerTargetCodeFrame (sl sh pl ph : Nat) (pc : BitVec 64)
    (code : List (BitVec 8)) (before after : BitVec 64 → BitVec 8)
    (programDomain : BitVec 64 → Prop)
    (writes : ∀ a, ¬ InitE.Op5.twoRegionBytes sl sh pl ph a → after a = before a)
    (loaded : bytesInMemHOL pc code before programDomain (InitE.Op5.twoRegionBytes sl sh pl ph)) :
    bytesInMemHOL pc code after programDomain (InitE.Op5.twoRegionBytes sl sh pl ph) :=
  target_code_frame sl sh pl ph pc code before after programDomain writes loaded

end InitE.Op5
