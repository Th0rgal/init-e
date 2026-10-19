import InitECandidate.Runtime.HeaderCarryPhases
import InitECandidate.Runtime.RunBoundedReaches
/-!
The actual header decoder from `decodeHeaderAt 25` to `decodeHeaderAt 56` is one carry.

All thirteen phases of the frozen body are proved as `HeaderCarryPhases` wrappers with
the same entry and exit predicate, and each of them is *one* actual program fragment of
the source path, so they join with `reaches_trans_budget` into a single `Reaches` whose
postcondition is exactly the uniform carry predicate and whose cost is the sum of the
phase budgets.

The state root word itself is generated earlier, by the actual early bytes chain from
`decodeHeaderAt 11` to `decodeHeaderAt 23` (`decode_header_early_bytes_written_state_root`)
and the difficulty phase to `decodeHeaderAt 25`; this module starts once that word, the
readable slice table and the `arr`/`h` locals are in place, and it delivers all of them
to the end of the fields, where the current/legacy suffix and the returned header
pointer are decoded.
-/
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
set_option maxRecDepth 100000
set_option maxHeartbeats 800000

/-- The summed budget of the thirteen actual phases from `decodeHeaderAt 25` to
`decodeHeaderAt 56`, in the order the source runs them. -/
def headerDecoderSpanCost (inputLimit : Nat) : Nat :=
  ((headerRlpFieldCost inputLimit + 35) + 2 * (headerRlpFieldCost inputLimit + 35) +
    (headerRlpFieldCost inputLimit + 1) + 1 * (headerRlpFieldCost inputLimit + 35) +
    (headerRlpFieldCost inputLimit + 1) + 2 * (headerRlpFieldCost inputLimit + 1) +
    (headerRlpFieldCost inputLimit + 35) + 1 * (headerRlpFieldCost inputLimit + 1) +
    (headerRlpFieldCost inputLimit + 1) + 1 * (headerRlpFieldCost inputLimit + 35) +
    (headerRlpFieldCost inputLimit + 1) + 1 * (headerRlpFieldCost inputLimit + 35) +
    2 * (headerRlpFieldCost inputLimit + 1))

/-- The carried state root word, slice table and decoder locals survive every actual
phase from `decodeHeaderAt 25` to `decodeHeaderAt 56`, within the summed phase budget. -/
theorem decode_header_carry_span {F : Type} (s : PanSemStateFiniteExact 64 F)
    (array count input inputLength scratch frame record word : BitVec 64) (ceiling inputLimit : Nat)
    (env : HeaderCarryEnv s array count input inputLength scratch frame record ceiling inputLimit)
    (entry : HeaderSuffixCarry s s array count input inputLength record word)
    (budget : headerDecoderSpanCost inputLimit ≤ s.clock) :
    Reaches s (decodeHeaderAt 25)
      (fun post => HeaderSuffixCarry s post array count input inputLength record word)
      (headerDecoderSpanCost inputLimit) (decodeHeaderAt 56) := by
  have span : headerDecoderSpanCost inputLimit =
    ((headerRlpFieldCost inputLimit + 35) + 2 * (headerRlpFieldCost inputLimit + 35) +
      (headerRlpFieldCost inputLimit + 1) + 1 * (headerRlpFieldCost inputLimit + 35) +
      (headerRlpFieldCost inputLimit + 1) + 2 * (headerRlpFieldCost inputLimit + 1) +
      (headerRlpFieldCost inputLimit + 35) + 1 * (headerRlpFieldCost inputLimit + 1) +
      (headerRlpFieldCost inputLimit + 1) + 1 * (headerRlpFieldCost inputLimit + 35) +
      (headerRlpFieldCost inputLimit + 1) + 1 * (headerRlpFieldCost inputLimit + 35) +
      2 * (headerRlpFieldCost inputLimit + 1))    := rfl
  rw [span] at budget
  have stage1 : Reaches s (decodeHeaderAt 25) (fun post => HeaderSuffixCarry s post array count input inputLength record word) (headerRlpFieldCost inputLimit + 35) (decodeHeaderAt 27) :=
    header_carry_first_word s s array count input inputLength scratch frame record word ceiling inputLimit env entry (by omega)
  have stage2 : Reaches s (decodeHeaderAt 25) (fun post => HeaderSuffixCarry s post array count input inputLength record word)
      ((headerRlpFieldCost inputLimit + 35) + 2 * (headerRlpFieldCost inputLimit + 35))      (decodeHeaderAt 31) :=
    reaches_trans_budget s (decodeHeaderAt 25) (decodeHeaderAt 27) (decodeHeaderAt 31) (fun post => HeaderSuffixCarry s post array count input inputLength record word)
      (fun post => HeaderSuffixCarry s post array count input inputLength record word)
      ((headerRlpFieldCost inputLimit + 35)) (2 * (headerRlpFieldCost inputLimit + 35)) (by omega) stage1
      (fun next carried clock => header_carry_early_words s next array count input inputLength scratch frame record word ceiling inputLimit env carried clock)
  have stage3 : Reaches s (decodeHeaderAt 25) (fun post => HeaderSuffixCarry s post array count input inputLength record word)
      ((headerRlpFieldCost inputLimit + 35) + 2 * (headerRlpFieldCost inputLimit + 35) +
        (headerRlpFieldCost inputLimit + 1))      (decodeHeaderAt 33) :=
    reaches_trans_budget s (decodeHeaderAt 25) (decodeHeaderAt 31) (decodeHeaderAt 33) (fun post => HeaderSuffixCarry s post array count input inputLength record word)
      (fun post => HeaderSuffixCarry s post array count input inputLength record word)
      ((headerRlpFieldCost inputLimit + 35) + 2 * (headerRlpFieldCost inputLimit + 35)) ((headerRlpFieldCost inputLimit + 1)) (by omega) stage2
      (fun next carried clock => header_carry_timestamp_field s next array count input inputLength scratch frame record word ceiling inputLimit env carried clock)
  have stage4 : Reaches s (decodeHeaderAt 25) (fun post => HeaderSuffixCarry s post array count input inputLength record word)
      ((headerRlpFieldCost inputLimit + 35) + 2 * (headerRlpFieldCost inputLimit + 35) +
        (headerRlpFieldCost inputLimit + 1) + 1 * (headerRlpFieldCost inputLimit + 35))      (decodeHeaderAt 35) :=
    reaches_trans_budget s (decodeHeaderAt 25) (decodeHeaderAt 33) (decodeHeaderAt 35) (fun post => HeaderSuffixCarry s post array count input inputLength record word)
      (fun post => HeaderSuffixCarry s post array count input inputLength record word)
      ((headerRlpFieldCost inputLimit + 35) + 2 * (headerRlpFieldCost inputLimit + 35) +
        (headerRlpFieldCost inputLimit + 1)) (1 * (headerRlpFieldCost inputLimit + 35)) (by omega) stage3
      (fun next carried clock => header_carry_timestamp_word s next array count input inputLength scratch frame record word ceiling inputLimit env carried clock)
  have stage5 : Reaches s (decodeHeaderAt 25) (fun post => HeaderSuffixCarry s post array count input inputLength record word)
      ((headerRlpFieldCost inputLimit + 35) + 2 * (headerRlpFieldCost inputLimit + 35) +
        (headerRlpFieldCost inputLimit + 1) + 1 * (headerRlpFieldCost inputLimit + 35) +
        (headerRlpFieldCost inputLimit + 1))      (decodeHeaderAt 38) :=
    reaches_trans_budget s (decodeHeaderAt 25) (decodeHeaderAt 35) (decodeHeaderAt 38) (fun post => HeaderSuffixCarry s post array count input inputLength record word)
      (fun post => HeaderSuffixCarry s post array count input inputLength record word)
      ((headerRlpFieldCost inputLimit + 35) + 2 * (headerRlpFieldCost inputLimit + 35) +
        (headerRlpFieldCost inputLimit + 1) + 1 * (headerRlpFieldCost inputLimit + 35)) ((headerRlpFieldCost inputLimit + 1)) (by omega) stage4
      (fun next carried clock => header_carry_extra_field s next array count input inputLength scratch frame record word ceiling inputLimit env carried clock)
  have stage6 : Reaches s (decodeHeaderAt 25) (fun post => HeaderSuffixCarry s post array count input inputLength record word)
      ((headerRlpFieldCost inputLimit + 35) + 2 * (headerRlpFieldCost inputLimit + 35) +
        (headerRlpFieldCost inputLimit + 1) + 1 * (headerRlpFieldCost inputLimit + 35) +
        (headerRlpFieldCost inputLimit + 1) + 2 * (headerRlpFieldCost inputLimit + 1))      (decodeHeaderAt 42) :=
    reaches_trans_budget s (decodeHeaderAt 25) (decodeHeaderAt 38) (decodeHeaderAt 42) (fun post => HeaderSuffixCarry s post array count input inputLength record word)
      (fun post => HeaderSuffixCarry s post array count input inputLength record word)
      ((headerRlpFieldCost inputLimit + 35) + 2 * (headerRlpFieldCost inputLimit + 35) +
        (headerRlpFieldCost inputLimit + 1) + 1 * (headerRlpFieldCost inputLimit + 35) +
        (headerRlpFieldCost inputLimit + 1)) (2 * (headerRlpFieldCost inputLimit + 1)) (by omega) stage5
      (fun next carried clock => header_carry_middle_bytes s next array count input inputLength scratch frame record word ceiling inputLimit env carried clock)
  have stage7 : Reaches s (decodeHeaderAt 25) (fun post => HeaderSuffixCarry s post array count input inputLength record word)
      ((headerRlpFieldCost inputLimit + 35) + 2 * (headerRlpFieldCost inputLimit + 35) +
        (headerRlpFieldCost inputLimit + 1) + 1 * (headerRlpFieldCost inputLimit + 35) +
        (headerRlpFieldCost inputLimit + 1) + 2 * (headerRlpFieldCost inputLimit + 1) +
        (headerRlpFieldCost inputLimit + 35))      (decodeHeaderAt 44) :=
    reaches_trans_budget s (decodeHeaderAt 25) (decodeHeaderAt 42) (decodeHeaderAt 44) (fun post => HeaderSuffixCarry s post array count input inputLength record word)
      (fun post => HeaderSuffixCarry s post array count input inputLength record word)
      ((headerRlpFieldCost inputLimit + 35) + 2 * (headerRlpFieldCost inputLimit + 35) +
        (headerRlpFieldCost inputLimit + 1) + 1 * (headerRlpFieldCost inputLimit + 35) +
        (headerRlpFieldCost inputLimit + 1) + 2 * (headerRlpFieldCost inputLimit + 1)) ((headerRlpFieldCost inputLimit + 35)) (by omega) stage6
      (fun next carried clock => header_carry_basefee s next array count input inputLength scratch frame record word ceiling inputLimit env carried clock)
  have stage8 : Reaches s (decodeHeaderAt 25) (fun post => HeaderSuffixCarry s post array count input inputLength record word)
      ((headerRlpFieldCost inputLimit + 35) + 2 * (headerRlpFieldCost inputLimit + 35) +
        (headerRlpFieldCost inputLimit + 1) + 1 * (headerRlpFieldCost inputLimit + 35) +
        (headerRlpFieldCost inputLimit + 1) + 2 * (headerRlpFieldCost inputLimit + 1) +
        (headerRlpFieldCost inputLimit + 35) + 1 * (headerRlpFieldCost inputLimit + 1))      (decodeHeaderAt 46) :=
    reaches_trans_budget s (decodeHeaderAt 25) (decodeHeaderAt 44) (decodeHeaderAt 46) (fun post => HeaderSuffixCarry s post array count input inputLength record word)
      (fun post => HeaderSuffixCarry s post array count input inputLength record word)
      ((headerRlpFieldCost inputLimit + 35) + 2 * (headerRlpFieldCost inputLimit + 35) +
        (headerRlpFieldCost inputLimit + 1) + 1 * (headerRlpFieldCost inputLimit + 35) +
        (headerRlpFieldCost inputLimit + 1) + 2 * (headerRlpFieldCost inputLimit + 1) +
        (headerRlpFieldCost inputLimit + 35)) (1 * (headerRlpFieldCost inputLimit + 1)) (by omega) stage7
      (fun next carried clock => header_carry_withdrawals_bytes s next array count input inputLength scratch frame record word ceiling inputLimit env carried clock)
  have stage9 : Reaches s (decodeHeaderAt 25) (fun post => HeaderSuffixCarry s post array count input inputLength record word)
      ((headerRlpFieldCost inputLimit + 35) + 2 * (headerRlpFieldCost inputLimit + 35) +
        (headerRlpFieldCost inputLimit + 1) + 1 * (headerRlpFieldCost inputLimit + 35) +
        (headerRlpFieldCost inputLimit + 1) + 2 * (headerRlpFieldCost inputLimit + 1) +
        (headerRlpFieldCost inputLimit + 35) + 1 * (headerRlpFieldCost inputLimit + 1) +
        (headerRlpFieldCost inputLimit + 1))      (decodeHeaderAt 47) :=
    reaches_trans_budget s (decodeHeaderAt 25) (decodeHeaderAt 46) (decodeHeaderAt 47) (fun post => HeaderSuffixCarry s post array count input inputLength record word)
      (fun post => HeaderSuffixCarry s post array count input inputLength record word)
      ((headerRlpFieldCost inputLimit + 35) + 2 * (headerRlpFieldCost inputLimit + 35) +
        (headerRlpFieldCost inputLimit + 1) + 1 * (headerRlpFieldCost inputLimit + 35) +
        (headerRlpFieldCost inputLimit + 1) + 2 * (headerRlpFieldCost inputLimit + 1) +
        (headerRlpFieldCost inputLimit + 35) + 1 * (headerRlpFieldCost inputLimit + 1)) ((headerRlpFieldCost inputLimit + 1)) (by omega) stage8
      (fun next carried clock => header_carry_blobgas_field s next array count input inputLength scratch frame record word ceiling inputLimit env carried clock)
  have stage10 : Reaches s (decodeHeaderAt 25) (fun post => HeaderSuffixCarry s post array count input inputLength record word)
      ((headerRlpFieldCost inputLimit + 35) + 2 * (headerRlpFieldCost inputLimit + 35) +
        (headerRlpFieldCost inputLimit + 1) + 1 * (headerRlpFieldCost inputLimit + 35) +
        (headerRlpFieldCost inputLimit + 1) + 2 * (headerRlpFieldCost inputLimit + 1) +
        (headerRlpFieldCost inputLimit + 35) + 1 * (headerRlpFieldCost inputLimit + 1) +
        (headerRlpFieldCost inputLimit + 1) + 1 * (headerRlpFieldCost inputLimit + 35))      (decodeHeaderAt 49) :=
    reaches_trans_budget s (decodeHeaderAt 25) (decodeHeaderAt 47) (decodeHeaderAt 49) (fun post => HeaderSuffixCarry s post array count input inputLength record word)
      (fun post => HeaderSuffixCarry s post array count input inputLength record word)
      ((headerRlpFieldCost inputLimit + 35) + 2 * (headerRlpFieldCost inputLimit + 35) +
        (headerRlpFieldCost inputLimit + 1) + 1 * (headerRlpFieldCost inputLimit + 35) +
        (headerRlpFieldCost inputLimit + 1) + 2 * (headerRlpFieldCost inputLimit + 1) +
        (headerRlpFieldCost inputLimit + 35) + 1 * (headerRlpFieldCost inputLimit + 1) +
        (headerRlpFieldCost inputLimit + 1)) (1 * (headerRlpFieldCost inputLimit + 35)) (by omega) stage9
      (fun next carried clock => header_carry_blobgas_word s next array count input inputLength scratch frame record word ceiling inputLimit env carried clock)
  have stage11 : Reaches s (decodeHeaderAt 25) (fun post => HeaderSuffixCarry s post array count input inputLength record word)
      ((headerRlpFieldCost inputLimit + 35) + 2 * (headerRlpFieldCost inputLimit + 35) +
        (headerRlpFieldCost inputLimit + 1) + 1 * (headerRlpFieldCost inputLimit + 35) +
        (headerRlpFieldCost inputLimit + 1) + 2 * (headerRlpFieldCost inputLimit + 1) +
        (headerRlpFieldCost inputLimit + 35) + 1 * (headerRlpFieldCost inputLimit + 1) +
        (headerRlpFieldCost inputLimit + 1) + 1 * (headerRlpFieldCost inputLimit + 35) +
        (headerRlpFieldCost inputLimit + 1))      (decodeHeaderAt 50) :=
    reaches_trans_budget s (decodeHeaderAt 25) (decodeHeaderAt 49) (decodeHeaderAt 50) (fun post => HeaderSuffixCarry s post array count input inputLength record word)
      (fun post => HeaderSuffixCarry s post array count input inputLength record word)
      ((headerRlpFieldCost inputLimit + 35) + 2 * (headerRlpFieldCost inputLimit + 35) +
        (headerRlpFieldCost inputLimit + 1) + 1 * (headerRlpFieldCost inputLimit + 35) +
        (headerRlpFieldCost inputLimit + 1) + 2 * (headerRlpFieldCost inputLimit + 1) +
        (headerRlpFieldCost inputLimit + 35) + 1 * (headerRlpFieldCost inputLimit + 1) +
        (headerRlpFieldCost inputLimit + 1) + 1 * (headerRlpFieldCost inputLimit + 35)) ((headerRlpFieldCost inputLimit + 1)) (by omega) stage10
      (fun next carried clock => header_carry_excess_blobgas_field s next array count input inputLength scratch frame record word ceiling inputLimit env carried clock)
  have stage12 : Reaches s (decodeHeaderAt 25) (fun post => HeaderSuffixCarry s post array count input inputLength record word)
      ((headerRlpFieldCost inputLimit + 35) + 2 * (headerRlpFieldCost inputLimit + 35) +
        (headerRlpFieldCost inputLimit + 1) + 1 * (headerRlpFieldCost inputLimit + 35) +
        (headerRlpFieldCost inputLimit + 1) + 2 * (headerRlpFieldCost inputLimit + 1) +
        (headerRlpFieldCost inputLimit + 35) + 1 * (headerRlpFieldCost inputLimit + 1) +
        (headerRlpFieldCost inputLimit + 1) + 1 * (headerRlpFieldCost inputLimit + 35) +
        (headerRlpFieldCost inputLimit + 1) + 1 * (headerRlpFieldCost inputLimit + 35))      (decodeHeaderAt 52) :=
    reaches_trans_budget s (decodeHeaderAt 25) (decodeHeaderAt 50) (decodeHeaderAt 52) (fun post => HeaderSuffixCarry s post array count input inputLength record word)
      (fun post => HeaderSuffixCarry s post array count input inputLength record word)
      ((headerRlpFieldCost inputLimit + 35) + 2 * (headerRlpFieldCost inputLimit + 35) +
        (headerRlpFieldCost inputLimit + 1) + 1 * (headerRlpFieldCost inputLimit + 35) +
        (headerRlpFieldCost inputLimit + 1) + 2 * (headerRlpFieldCost inputLimit + 1) +
        (headerRlpFieldCost inputLimit + 35) + 1 * (headerRlpFieldCost inputLimit + 1) +
        (headerRlpFieldCost inputLimit + 1) + 1 * (headerRlpFieldCost inputLimit + 35) +
        (headerRlpFieldCost inputLimit + 1)) (1 * (headerRlpFieldCost inputLimit + 35)) (by omega) stage11
      (fun next carried clock => header_carry_excess_blobgas_word s next array count input inputLength scratch frame record word ceiling inputLimit env carried clock)
  have stage13 : Reaches s (decodeHeaderAt 25) (fun post => HeaderSuffixCarry s post array count input inputLength record word)
      ((headerRlpFieldCost inputLimit + 35) + 2 * (headerRlpFieldCost inputLimit + 35) +
        (headerRlpFieldCost inputLimit + 1) + 1 * (headerRlpFieldCost inputLimit + 35) +
        (headerRlpFieldCost inputLimit + 1) + 2 * (headerRlpFieldCost inputLimit + 1) +
        (headerRlpFieldCost inputLimit + 35) + 1 * (headerRlpFieldCost inputLimit + 1) +
        (headerRlpFieldCost inputLimit + 1) + 1 * (headerRlpFieldCost inputLimit + 35) +
        (headerRlpFieldCost inputLimit + 1) + 1 * (headerRlpFieldCost inputLimit + 35) +
        2 * (headerRlpFieldCost inputLimit + 1))      (decodeHeaderAt 56) :=
    reaches_trans_budget s (decodeHeaderAt 25) (decodeHeaderAt 52) (decodeHeaderAt 56) (fun post => HeaderSuffixCarry s post array count input inputLength record word)
      (fun post => HeaderSuffixCarry s post array count input inputLength record word)
      ((headerRlpFieldCost inputLimit + 35) + 2 * (headerRlpFieldCost inputLimit + 35) +
        (headerRlpFieldCost inputLimit + 1) + 1 * (headerRlpFieldCost inputLimit + 35) +
        (headerRlpFieldCost inputLimit + 1) + 2 * (headerRlpFieldCost inputLimit + 1) +
        (headerRlpFieldCost inputLimit + 35) + 1 * (headerRlpFieldCost inputLimit + 1) +
        (headerRlpFieldCost inputLimit + 1) + 1 * (headerRlpFieldCost inputLimit + 35) +
        (headerRlpFieldCost inputLimit + 1) + 1 * (headerRlpFieldCost inputLimit + 35)) (2 * (headerRlpFieldCost inputLimit + 1)) (by omega) stage12
      (fun next carried clock => header_carry_last_bytes s next array count input inputLength scratch frame record word ceiling inputLimit env carried clock)
  exact reaches_mono s _ _ _ _ _ _ (Nat.le_of_eq span.symm) (fun _ kept => kept) stage13

#print axioms decode_header_carry_span
end InitECandidate.Runtime
