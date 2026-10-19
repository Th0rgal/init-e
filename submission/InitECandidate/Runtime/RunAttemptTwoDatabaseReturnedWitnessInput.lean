import InitECandidate.Runtime.RunAttemptTwoDatabaseReturnedWitnessLocals
import InitECandidate.Runtime.NodedbInputCost
/-!
Uniform input budget for the two actual database calls.

The decoded count of either database builder is bounded by one quarter of the
input length, so both actual calls are covered uniformly by the same
input-dependent call budget: the two-call composition runs in
`2 * nodedbInputCallCost inputLimit` without any count-specific budget premise.
-/
namespace InitECandidate.Runtime
open Flapjack Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
set_option maxRecDepth 100000
set_option maxHeartbeats 800000

/-- The two actual database declarations run within the uniform input budget and
keep both witnesses, the caller locals modulo the two updates and the caller's
old protected memory. -/
theorem run_attempt_two_database_returned_witness_input {F : Type} (s : PanSemStateFiniteExact 64 F)
    (si heap total₁ array₁ total₂ array₂ input inputLength statePad pad output : BitVec 64)
    (inputLimit : Nat) (inputBound : inputLength.toNat ≤ inputLimit) (inputCap : inputLimit ≤ 134217712)
    (atSi : s.locals.lookup (ofString "si") = some (.val (.word si)))
    (linked₁ : WitnessArrayLinked s si 40 48 array₁ total₁ input inputLength heap)
    (linked₂ : WitnessArrayLinked s si 56 64 array₂ total₂ input inputLength heap)
    (code : s.code = originalRuntimeCode)
    (atHeap : s.globals.lookup (ofString "heap_ptr") = some (.val (.word heap)))
    (aligned : heap.toNat % 8 = 0) (capped : heap.toNat ≤ 33806089496)
    (atState : s.globals.lookup (ofString "keccak_st") = some (.val (.word statePad)))
    (atPad : s.globals.lookup (ofString "keccak_pad") = some (.val (.word pad)))
    (atOutput : s.globals.lookup (ofString "mpt_hash_scratch") = some (.val (.word output)))
    (inputSmall : inputLength.toNat ≤ 134217712) (outputAligned : output.toNat % 8 = 0)
    (windows₁ : total₁ ≠ 0 → statePad.toNat + 200 ≤ array₁.toNat ∧ pad.toNat + 136 ≤ array₁.toNat ∧
      output.toNat + 32 ≤ array₁.toNat)
    (windows₂ : total₂ ≠ 0 → statePad.toNat + 200 ≤ array₂.toNat ∧ pad.toNat + 136 ≤ array₂.toNat ∧
      output.toNat + 32 ≤ array₂.toNat)
    (arena : ∀ a : BitVec 64, a.toNat % 8 = 0 → heap.toNat ≤ a.toNat → a.toNat < 33806089496 →
      s.memaddrs a)
    (budget : 2 * nodedbInputCallCost inputLimit ≤ s.clock)
    (ceiling : Nat)
    (stateBelow : statePad.toNat + 200 ≤ ceiling) (padBelow : pad.toNat + 136 ≤ ceiling)
    (outputBelow : output.toNat + 32 ≤ ceiling)
    (recordAbove : ceiling ≤ si.toNat) (recordBefore : si.toNat + 88 ≤ heap.toNat)
    (arrayAbove₁ : total₁.toNat = 0 ∨ ceiling ≤ array₁.toNat)
    (arrayAbove₂ : total₂.toNat = 0 ∨ ceiling ≤ array₂.toNat) :
    Reaches s (runAttemptAt 9)
      (fun final => final.memaddrs = s.memaddrs ∧ final.code = s.code ∧
        final.globals.lookup (ofString "keccak_st") = some (.val (.word statePad)) ∧
        final.globals.lookup (ofString "keccak_pad") = some (.val (.word pad)) ∧
        final.globals.lookup (ofString "mpt_hash_scratch") = some (.val (.word output)) ∧
        (∃ finalHeap : BitVec 64, final.globals.lookup (ofString "heap_ptr") = some (.val (.word finalHeap)) ∧
          heap.toNat ≤ finalHeap.toNat ∧ finalHeap.toNat % 8 = 0 ∧ finalHeap.toNat ≤ 33806089496 ∧
          WitnessArrayLinked final si 40 48 array₁ total₁ input inputLength finalHeap ∧
          WitnessArrayLinked final si 56 64 array₂ total₂ input inputLength finalHeap ∧
          (∀ a : BitVec 64, a.toNat % 8 = 0 → finalHeap.toNat ≤ a.toNat → a.toNat < 33806089496 →
            final.memaddrs a) ∧
          (∃ intermediateHeap : BitVec 64, heap.toNat ≤ intermediateHeap.toNat ∧
            intermediateHeap.toNat ≤ finalHeap.toNat ∧
            final.locals = (s.locals.update (ofString "nodedb",.val (.word heap))).update
              (ofString "codedb",.val (.word intermediateHeap)))) ∧
        (∀ w : BitVec 64, w.toNat < heap.toNat → ¬ MWin statePad 200 w →
          ¬ MWin pad 136 w → ¬ MWin output 32 w → final.memory w = s.memory w))
      (2 * nodedbInputCallCost inputLimit) (runAttemptAt 11) := by
  have first := nodedb_call_cost_le_input total₁ inputLength inputLimit linked₁.countBound inputBound inputCap
  have second := nodedb_call_cost_le_input total₂ inputLength inputLimit linked₂.countBound inputBound inputCap
  have composed := run_attempt_two_database_returned_witness_locals s si heap total₁ array₁ total₂ array₂ input
    inputLength statePad pad output atSi linked₁ linked₂ code atHeap aligned capped atState atPad atOutput
    inputSmall outputAligned windows₁ windows₂ arena (by omega) ceiling stateBelow padBelow outputBelow
    recordAbove recordBefore arrayAbove₁ arrayAbove₂
  exact reaches_mono s (runAttemptAt 9) (runAttemptAt 11) _ _ _ _ (by omega) (fun _ h => h) composed

#print axioms run_attempt_two_database_returned_witness_input
end InitECandidate.Runtime
