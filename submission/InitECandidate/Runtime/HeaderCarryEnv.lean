import InitECandidate.Runtime.HeaderSuffixCarry
/-!
The stable facts a header-decoder phase needs from the entry state.

Every phase carrier of the actual header decoder takes the same block of premises: the
slice-table geometry (`before`, `fits`, the count bound), the record geometry
(`recordFits`), the workspace arrangement (`scratch`, `frame`, `orderedFrame`,
`framePositive`, `scratchBelow`), the input budget bounds and the facts about the
entry state itself (`scratch_ptr`, `frame_mem_ptr`, the frozen code and the arena).

Only the last group changes from phase to phase; the rest are properties of the
parameters, so they are collected once in `HeaderCarryEnv` and reused by every phase
wrapper.  `HeaderCarryEnv` is always stated against the reference state of the
composition, and the per-phase state facts are recovered from `HeaderSuffixCarry`,
whose domain, code and global agreement transport them to the current state.
-/
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
set_option maxRecDepth 100000
set_option maxHeartbeats 400000

/-- The phase-independent premises of the actual header decoder. -/
structure HeaderCarryEnv {F : Type} (s : PanSemStateFiniteExact 64 F)
    (array count input inputLength scratch frame record : BitVec 64) (ceiling inputLimit : Nat) : Prop where
  countBound : 21 ≤ count.toNat
  before : array.toNat + count.toNat * 16 ≤ record.toNat
  recordFits : record.toNat + 248 < 2^64
  above : ceiling ≤ array.toNat
  fits : array.toNat + count.toNat * 16 ≤ 2^64
  inputBound : inputLength.toNat ≤ inputLimit
  limitBound : inputLimit + 9 < 2^64
  scratchGlobal : s.globals.lookup (ofString "scratch_ptr") = some (.val (.word scratch))
  frameGlobal : s.globals.lookup (ofString "frame_mem_ptr") = some (.val (.word frame))
  code : s.code = originalRuntimeCode
  orderedFrame : frame ≤ scratch
  framePositive : 0 < frame.toNat
  scratchBelow : scratch.toNat ≤ ceiling
  arena : ∀ address : BitVec 64, frame.toNat ≤ address.toNat → address.toNat < ceiling → s.memaddrs address

/-- The decoder workspace globals at the current state, transported through the carry
predicate's global agreement. -/
theorem HeaderCarryEnv.scratchGlobalAt {F : Type} {s next : PanSemStateFiniteExact 64 F}
    {array count input inputLength record word scratch frame : BitVec 64} {ceiling inputLimit : Nat}
    (env : HeaderCarryEnv s array count input inputLength scratch frame record ceiling inputLimit)
    (carry : HeaderSuffixCarry s next array count input inputLength record word) :
    next.globals.lookup (ofString "scratch_ptr") = some (.val (.word scratch)) :=
  (carry.2.2.2.1 (ofString "scratch_ptr")).trans env.scratchGlobal

/-- The header-record workspace global at the current state. -/
theorem HeaderCarryEnv.frameGlobalAt {F : Type} {s next : PanSemStateFiniteExact 64 F}
    {array count input inputLength record word scratch frame : BitVec 64} {ceiling inputLimit : Nat}
    (env : HeaderCarryEnv s array count input inputLength scratch frame record ceiling inputLimit)
    (carry : HeaderSuffixCarry s next array count input inputLength record word) :
    next.globals.lookup (ofString "frame_mem_ptr") = some (.val (.word frame)) :=
  (carry.2.2.2.1 (ofString "frame_mem_ptr")).trans env.frameGlobal

/-- The frozen runtime code at the current state. -/
theorem HeaderCarryEnv.codeAt {F : Type} {s next : PanSemStateFiniteExact 64 F}
    {array count input inputLength record word scratch frame : BitVec 64} {ceiling inputLimit : Nat}
    (env : HeaderCarryEnv s array count input inputLength scratch frame record ceiling inputLimit)
    (carry : HeaderSuffixCarry s next array count input inputLength record word) :
    next.code = originalRuntimeCode :=
  carry.2.2.1.trans env.code

/-- The allocator arena at the current state. -/
theorem HeaderCarryEnv.arenaAt {F : Type} {s next : PanSemStateFiniteExact 64 F}
    {array count input inputLength record word scratch frame : BitVec 64} {ceiling inputLimit : Nat}
    (env : HeaderCarryEnv s array count input inputLength scratch frame record ceiling inputLimit)
    (carry : HeaderSuffixCarry s next array count input inputLength record word) :
    ∀ address : BitVec 64, frame.toNat ≤ address.toNat → address.toNat < ceiling → next.memaddrs address := by
  intro address low high
  rw [carry.2.1]
  exact env.arena address low high

#print axioms HeaderCarryEnv.scratchGlobalAt
#print axioms HeaderCarryEnv.frameGlobalAt
#print axioms HeaderCarryEnv.codeAt
#print axioms HeaderCarryEnv.arenaAt
end InitECandidate.Runtime
