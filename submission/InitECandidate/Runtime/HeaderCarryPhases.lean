import InitECandidate.Runtime.HeaderCarryEnv
import InitECandidate.Runtime.DecodeHeaderFirstWordStateRoot
import InitECandidate.Runtime.DecodeHeaderEarlyWordsStateRoot
import InitECandidate.Runtime.DecodeHeaderTimestampFieldStateRoot
import InitECandidate.Runtime.DecodeHeaderTimestampStateRoot
import InitECandidate.Runtime.DecodeHeaderExtraFieldCarry
import InitECandidate.Runtime.HeaderMiddleBytesStateRoot
import InitECandidate.Runtime.DecodeHeaderBasefeeCarry
import InitECandidate.Runtime.HeaderWithdrawalsBytesStateRoot
import InitECandidate.Runtime.DecodeHeaderBlobGasFieldStateRoot
import InitECandidate.Runtime.DecodeHeaderBlobGasStateRoot
import InitECandidate.Runtime.DecodeHeaderExcessBlobGasFieldStateRoot
import InitECandidate.Runtime.DecodeHeaderExcessBlobGasStateRoot
import InitECandidate.Runtime.HeaderLastBytesStateRoot
/-!
Every actual phase of the header decoder carries the uniform decoder context.

Each theorem below is one phase of the frozen body, from `decodeHeaderAt 25` to
`decodeHeaderAt 56`, stated uniformly: given the phase-independent premises of
`HeaderCarryEnv` against the reference state and the uniform carry predicate
`HeaderSuffixCarry` at the phase entry, the phase reaches its successor with the same
carry predicate at the reached state and costs exactly its own carrier's budget.

The heavier lifting (the state root word, the slice table and the `arr`/`h` locals) is
already done by the phase carriers; this module only transports the entry facts through
the carry predicate and re-establishes it at the exit.  Word-field spans go through
`header_carry_of_word_frame`, bytes spans through `header_carry_of_bytes_frame`, and the
single-field phases through `header_carry_intro`.  The span costs are stated with the
numerals their span lists have, so the chain of `DecodeHeaderCarryChain` can add them
linearly.
-/
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
set_option maxRecDepth 100000
set_option maxHeartbeats 400000

/-- `decodeHeaderAt 25 -> 27`: the first word field keeps the carry. -/
theorem header_carry_first_word {F : Type} (s next : PanSemStateFiniteExact 64 F)
    (array count input inputLength scratch frame record word : BitVec 64) (ceiling inputLimit : Nat)
    (env : HeaderCarryEnv s array count input inputLength scratch frame record ceiling inputLimit)
    (carry : HeaderSuffixCarry s next array count input inputLength record word)
    (clock : headerRlpFieldCost inputLimit + 35 ≤ next.clock) :
    Reaches next (decodeHeaderAt 25)
      (fun post => HeaderSuffixCarry s post array count input inputLength record word)
      (headerRlpFieldCost inputLimit + 35) (decodeHeaderAt 27) := by
  have countBound := env.countBound
  have rootMem := carry.1
  have domain := carry.2.1
  have codeEq := carry.2.2.1
  have globalsEq := carry.2.2.2.1
  have tableN := carry.2.2.2.2.1
  have atArrayN := carry.2.2.2.2.2.1
  have atRecordN := carry.2.2.2.2.2.2
  refine reaches_mono next (decodeHeaderAt 25) (decodeHeaderAt 27) _ _ _ _ (le_refl _) ?_
    (decode_header_first_word_keeps_state_root next array count input inputLength scratch frame record word ceiling
      inputLimit (by omega) atArrayN atRecordN env.before env.recordFits tableN env.above env.fits env.inputBound
      env.limitBound (env.scratchGlobalAt carry) (env.frameGlobalAt carry) (env.codeAt carry) env.orderedFrame
      env.framePositive env.scratchBelow (env.arenaAt carry) clock rootMem)
  intro post facts
  obtain ⟨root,dom,code,globals,table,atArray,atRecord,_⟩ := facts
  exact header_carry_intro s next post array count input inputLength record word carry root dom code globals table
    atArray atRecord

/-- `decodeHeaderAt 27 -> 31`: the two early word fields keep the carry. -/
theorem header_carry_early_words {F : Type} (s next : PanSemStateFiniteExact 64 F)
    (array count input inputLength scratch frame record word : BitVec 64) (ceiling inputLimit : Nat)
    (env : HeaderCarryEnv s array count input inputLength scratch frame record ceiling inputLimit)
    (carry : HeaderSuffixCarry s next array count input inputLength record word)
    (clock : 2 * (headerRlpFieldCost inputLimit + 35) ≤ next.clock) :
    Reaches next (decodeHeaderAt 27)
      (fun post => HeaderSuffixCarry s post array count input inputLength record word)
      (2 * (headerRlpFieldCost inputLimit + 35)) (decodeHeaderAt 31) := by
  have countBound := env.countBound
  have rootMem := carry.1
  have domain := carry.2.1
  have codeEq := carry.2.2.1
  have globalsEq := carry.2.2.2.1
  have tableN := carry.2.2.2.2.1
  have atArrayN := carry.2.2.2.2.2.1
  have atRecordN := carry.2.2.2.2.2.2
  refine reaches_mono next (decodeHeaderAt 27) (decodeHeaderAt 31) _ _ _ _ (le_refl _) ?_
    (decode_header_early_words_keeps_state_root next array count input inputLength scratch frame record word ceiling
      inputLimit (by omega) atArrayN atRecordN env.before env.recordFits tableN env.above env.fits env.inputBound
      env.limitBound (env.scratchGlobalAt carry) (env.frameGlobalAt carry) (env.codeAt carry) env.orderedFrame
      env.framePositive env.scratchBelow (env.arenaAt carry) clock rootMem)
  intro post facts
  exact header_carry_of_word_frame s next post array count input inputLength record word ceiling carry facts

/-- `decodeHeaderAt 31 -> 33`: the timestamp field and its width guard keep the carry. -/
theorem header_carry_timestamp_field {F : Type} (s next : PanSemStateFiniteExact 64 F)
    (array count input inputLength scratch frame record word : BitVec 64) (ceiling inputLimit : Nat)
    (env : HeaderCarryEnv s array count input inputLength scratch frame record ceiling inputLimit)
    (carry : HeaderSuffixCarry s next array count input inputLength record word)
    (clock : headerRlpFieldCost inputLimit + 1 ≤ next.clock) :
    Reaches next (decodeHeaderAt 31)
      (fun post => HeaderSuffixCarry s post array count input inputLength record word)
      (headerRlpFieldCost inputLimit + 1) (decodeHeaderAt 33) := by
  have countBound := env.countBound
  have rootMem := carry.1
  have domain := carry.2.1
  have codeEq := carry.2.2.1
  have globalsEq := carry.2.2.2.1
  have tableN := carry.2.2.2.2.1
  have atArrayN := carry.2.2.2.2.2.1
  have atRecordN := carry.2.2.2.2.2.2
  refine reaches_mono next (decodeHeaderAt 31) (decodeHeaderAt 33) _ _ _ _ (le_refl _) ?_
    (decode_header_timestamp_field_keeps_state_root next array count input inputLength scratch frame record word ceiling
      inputLimit atArrayN atRecordN env.before env.recordFits tableN (by omega) env.above env.fits env.inputBound
      env.limitBound (env.scratchGlobalAt carry) (env.frameGlobalAt carry) (env.codeAt carry) env.orderedFrame
      env.framePositive env.scratchBelow (env.arenaAt carry) clock rootMem)
  intro post facts
  obtain ⟨root,dom,code,globals,table,atArray,atRecord,_⟩ := facts
  exact header_carry_intro s next post array count input inputLength record word carry root dom code globals table
    atArray atRecord

/-- `decodeHeaderAt 33 -> 35`: the timestamp word keeps the carry. -/
theorem header_carry_timestamp_word {F : Type} (s next : PanSemStateFiniteExact 64 F)
    (array count input inputLength scratch frame record word : BitVec 64) (ceiling inputLimit : Nat)
    (env : HeaderCarryEnv s array count input inputLength scratch frame record ceiling inputLimit)
    (carry : HeaderSuffixCarry s next array count input inputLength record word)
    (clock : 1 * (headerRlpFieldCost inputLimit + 35) ≤ next.clock) :
    Reaches next (decodeHeaderAt 33)
      (fun post => HeaderSuffixCarry s post array count input inputLength record word)
      (1 * (headerRlpFieldCost inputLimit + 35)) (decodeHeaderAt 35) := by
  have countBound := env.countBound
  have rootMem := carry.1
  have domain := carry.2.1
  have codeEq := carry.2.2.1
  have globalsEq := carry.2.2.2.1
  have tableN := carry.2.2.2.2.1
  have atArrayN := carry.2.2.2.2.2.1
  have atRecordN := carry.2.2.2.2.2.2
  refine reaches_mono next (decodeHeaderAt 33) (decodeHeaderAt 35) _ _ _ _ (le_refl _) ?_
    (decode_header_timestamp_keeps_state_root next array count input inputLength scratch frame record word ceiling
      inputLimit (by omega) atArrayN atRecordN env.before env.recordFits tableN env.above env.fits env.inputBound
      env.limitBound (env.scratchGlobalAt carry) (env.frameGlobalAt carry) (env.codeAt carry) env.orderedFrame
      env.framePositive env.scratchBelow (env.arenaAt carry) clock rootMem)
  intro post facts
  exact header_carry_of_word_frame s next post array count input inputLength record word ceiling carry facts

/-- `decodeHeaderAt 35 -> 38`: the extra-data field and its two stores keep the carry. -/
theorem header_carry_extra_field {F : Type} (s next : PanSemStateFiniteExact 64 F)
    (array count input inputLength scratch frame record word : BitVec 64) (ceiling inputLimit : Nat)
    (env : HeaderCarryEnv s array count input inputLength scratch frame record ceiling inputLimit)
    (carry : HeaderSuffixCarry s next array count input inputLength record word)
    (clock : headerRlpFieldCost inputLimit + 1 ≤ next.clock) :
    Reaches next (decodeHeaderAt 35)
      (fun post => HeaderSuffixCarry s post array count input inputLength record word)
      (headerRlpFieldCost inputLimit + 1) (decodeHeaderAt 38) := by
  have countBound := env.countBound
  have rootMem := carry.1
  have domain := carry.2.1
  have codeEq := carry.2.2.1
  have globalsEq := carry.2.2.2.1
  have tableN := carry.2.2.2.2.1
  have atArrayN := carry.2.2.2.2.2.1
  have atRecordN := carry.2.2.2.2.2.2
  refine reaches_mono next (decodeHeaderAt 35) (decodeHeaderAt 38) _ _ _ _ (le_refl _) ?_
    (decode_header_extra_field_ready next array count input inputLength scratch frame record word ceiling
      inputLimit atArrayN atRecordN env.before env.recordFits tableN (by omega) env.above env.fits env.inputBound
      env.limitBound (env.scratchGlobalAt carry) (env.frameGlobalAt carry) (env.codeAt carry) env.orderedFrame
      env.framePositive env.scratchBelow (env.arenaAt carry) clock rootMem)
  intro post facts
  obtain ⟨root,dom,code,globals,table,atArray,atRecord⟩ := facts
  exact header_carry_intro s next post array count input inputLength record word carry root dom code globals table
    atArray atRecord

/-- `decodeHeaderAt 38 -> 42`: the middle bytes fields keep the carry. -/
theorem header_carry_middle_bytes {F : Type} (s next : PanSemStateFiniteExact 64 F)
    (array count input inputLength scratch frame record word : BitVec 64) (ceiling inputLimit : Nat)
    (env : HeaderCarryEnv s array count input inputLength scratch frame record ceiling inputLimit)
    (carry : HeaderSuffixCarry s next array count input inputLength record word)
    (clock : 2 * (headerRlpFieldCost inputLimit + 1) ≤ next.clock) :
    Reaches next (decodeHeaderAt 38)
      (fun post => HeaderSuffixCarry s post array count input inputLength record word)
      (2 * (headerRlpFieldCost inputLimit + 1)) (decodeHeaderAt 42) := by
  have countBound := env.countBound
  have rootMem := carry.1
  have domain := carry.2.1
  have codeEq := carry.2.2.1
  have globalsEq := carry.2.2.2.1
  have tableN := carry.2.2.2.2.1
  have atArrayN := carry.2.2.2.2.2.1
  have atRecordN := carry.2.2.2.2.2.2
  refine reaches_mono next (decodeHeaderAt 38) (decodeHeaderAt 42) _ _ _ _ (le_refl _) ?_
    (decode_header_middle_bytes_keeps_state_root next array count input inputLength scratch frame record word ceiling
      inputLimit (by omega) atArrayN atRecordN env.before env.recordFits tableN env.above env.fits env.inputBound
      env.limitBound (env.scratchGlobalAt carry) (env.frameGlobalAt carry) (env.codeAt carry) env.orderedFrame
      env.framePositive env.scratchBelow (env.arenaAt carry) clock rootMem)
  intro post facts
  exact header_carry_of_bytes_frame s next post array count input inputLength record word ceiling carry facts

/-- `decodeHeaderAt 42 -> 44`: the base-fee field and its four-limb store keep the carry. -/
theorem header_carry_basefee {F : Type} (s next : PanSemStateFiniteExact 64 F)
    (array count input inputLength scratch frame record word : BitVec 64) (ceiling inputLimit : Nat)
    (env : HeaderCarryEnv s array count input inputLength scratch frame record ceiling inputLimit)
    (carry : HeaderSuffixCarry s next array count input inputLength record word)
    (clock : headerRlpFieldCost inputLimit + 35 ≤ next.clock) :
    Reaches next (decodeHeaderAt 42)
      (fun post => HeaderSuffixCarry s post array count input inputLength record word)
      (headerRlpFieldCost inputLimit + 35) (decodeHeaderAt 44) := by
  have countBound := env.countBound
  have rootMem := carry.1
  have domain := carry.2.1
  have codeEq := carry.2.2.1
  have globalsEq := carry.2.2.2.1
  have tableN := carry.2.2.2.2.1
  have atArrayN := carry.2.2.2.2.2.1
  have atRecordN := carry.2.2.2.2.2.2
  refine reaches_mono next (decodeHeaderAt 42) (decodeHeaderAt 44) _ _ _ _ (le_refl _) ?_
    (decode_header_basefee_ready next array count input inputLength scratch frame record word ceiling
      inputLimit atArrayN atRecordN env.before env.recordFits tableN (by omega) env.above env.fits env.inputBound
      env.limitBound (env.scratchGlobalAt carry) (env.frameGlobalAt carry) (env.codeAt carry) env.orderedFrame
      env.framePositive env.scratchBelow (env.arenaAt carry) clock rootMem)
  intro post facts
  obtain ⟨root,dom,code,globals,table,atArray,atRecord⟩ := facts
  exact header_carry_intro s next post array count input inputLength record word carry root dom code globals table
    atArray atRecord

/-- `decodeHeaderAt 44 -> 46`: the withdrawals-root field keeps the carry. -/
theorem header_carry_withdrawals_bytes {F : Type} (s next : PanSemStateFiniteExact 64 F)
    (array count input inputLength scratch frame record word : BitVec 64) (ceiling inputLimit : Nat)
    (env : HeaderCarryEnv s array count input inputLength scratch frame record ceiling inputLimit)
    (carry : HeaderSuffixCarry s next array count input inputLength record word)
    (clock : 1 * (headerRlpFieldCost inputLimit + 1) ≤ next.clock) :
    Reaches next (decodeHeaderAt 44)
      (fun post => HeaderSuffixCarry s post array count input inputLength record word)
      (1 * (headerRlpFieldCost inputLimit + 1)) (decodeHeaderAt 46) := by
  have countBound := env.countBound
  have rootMem := carry.1
  have domain := carry.2.1
  have codeEq := carry.2.2.1
  have globalsEq := carry.2.2.2.1
  have tableN := carry.2.2.2.2.1
  have atArrayN := carry.2.2.2.2.2.1
  have atRecordN := carry.2.2.2.2.2.2
  refine reaches_mono next (decodeHeaderAt 44) (decodeHeaderAt 46) _ _ _ _ (le_refl _) ?_
    (decode_header_withdrawals_bytes_keeps_state_root next array count input inputLength scratch frame record word
      ceiling inputLimit (by omega) atArrayN atRecordN env.before env.recordFits tableN env.above env.fits
      env.inputBound env.limitBound (env.scratchGlobalAt carry) (env.frameGlobalAt carry) (env.codeAt carry)
      env.orderedFrame env.framePositive env.scratchBelow (env.arenaAt carry) clock rootMem)
  intro post facts
  exact header_carry_of_bytes_frame s next post array count input inputLength record word ceiling carry facts

/-- `decodeHeaderAt 46 -> 47`: the blob-gas field keeps the carry. -/
theorem header_carry_blobgas_field {F : Type} (s next : PanSemStateFiniteExact 64 F)
    (array count input inputLength scratch frame record word : BitVec 64) (ceiling inputLimit : Nat)
    (env : HeaderCarryEnv s array count input inputLength scratch frame record ceiling inputLimit)
    (carry : HeaderSuffixCarry s next array count input inputLength record word)
    (clock : headerRlpFieldCost inputLimit + 1 ≤ next.clock) :
    Reaches next (decodeHeaderAt 46)
      (fun post => HeaderSuffixCarry s post array count input inputLength record word)
      (headerRlpFieldCost inputLimit + 1) (decodeHeaderAt 47) := by
  have countBound := env.countBound
  have rootMem := carry.1
  have domain := carry.2.1
  have codeEq := carry.2.2.1
  have globalsEq := carry.2.2.2.1
  have tableN := carry.2.2.2.2.1
  have atArrayN := carry.2.2.2.2.2.1
  have atRecordN := carry.2.2.2.2.2.2
  refine reaches_mono next (decodeHeaderAt 46) (decodeHeaderAt 47) _ _ _ _ (le_refl _) ?_
    (decode_header_blobgas_field_keeps_state_root next array count input inputLength scratch frame record word ceiling
      inputLimit atArrayN atRecordN env.before env.recordFits tableN (by omega) env.above env.fits env.inputBound
      env.limitBound (env.scratchGlobalAt carry) (env.frameGlobalAt carry) (env.codeAt carry) env.orderedFrame
      env.framePositive env.scratchBelow (env.arenaAt carry) clock rootMem)
  intro post facts
  obtain ⟨root,dom,code,globals,table,atArray,atRecord,_⟩ := facts
  exact header_carry_intro s next post array count input inputLength record word carry root dom code globals table
    atArray atRecord

/-- `decodeHeaderAt 47 -> 49`: the blob-gas word keeps the carry. -/
theorem header_carry_blobgas_word {F : Type} (s next : PanSemStateFiniteExact 64 F)
    (array count input inputLength scratch frame record word : BitVec 64) (ceiling inputLimit : Nat)
    (env : HeaderCarryEnv s array count input inputLength scratch frame record ceiling inputLimit)
    (carry : HeaderSuffixCarry s next array count input inputLength record word)
    (clock : 1 * (headerRlpFieldCost inputLimit + 35) ≤ next.clock) :
    Reaches next (decodeHeaderAt 47)
      (fun post => HeaderSuffixCarry s post array count input inputLength record word)
      (1 * (headerRlpFieldCost inputLimit + 35)) (decodeHeaderAt 49) := by
  have countBound := env.countBound
  have rootMem := carry.1
  have domain := carry.2.1
  have codeEq := carry.2.2.1
  have globalsEq := carry.2.2.2.1
  have tableN := carry.2.2.2.2.1
  have atArrayN := carry.2.2.2.2.2.1
  have atRecordN := carry.2.2.2.2.2.2
  refine reaches_mono next (decodeHeaderAt 47) (decodeHeaderAt 49) _ _ _ _ (le_refl _) ?_
    (decode_header_blobgas_keeps_state_root next array count input inputLength scratch frame record word ceiling
      inputLimit (by omega) atArrayN atRecordN env.before env.recordFits tableN env.above env.fits env.inputBound
      env.limitBound (env.scratchGlobalAt carry) (env.frameGlobalAt carry) (env.codeAt carry) env.orderedFrame
      env.framePositive env.scratchBelow (env.arenaAt carry) clock rootMem)
  intro post facts
  exact header_carry_of_word_frame s next post array count input inputLength record word ceiling carry facts

/-- `decodeHeaderAt 49 -> 50`: the excess-blob-gas field keeps the carry. -/
theorem header_carry_excess_blobgas_field {F : Type} (s next : PanSemStateFiniteExact 64 F)
    (array count input inputLength scratch frame record word : BitVec 64) (ceiling inputLimit : Nat)
    (env : HeaderCarryEnv s array count input inputLength scratch frame record ceiling inputLimit)
    (carry : HeaderSuffixCarry s next array count input inputLength record word)
    (clock : headerRlpFieldCost inputLimit + 1 ≤ next.clock) :
    Reaches next (decodeHeaderAt 49)
      (fun post => HeaderSuffixCarry s post array count input inputLength record word)
      (headerRlpFieldCost inputLimit + 1) (decodeHeaderAt 50) := by
  have countBound := env.countBound
  have rootMem := carry.1
  have domain := carry.2.1
  have codeEq := carry.2.2.1
  have globalsEq := carry.2.2.2.1
  have tableN := carry.2.2.2.2.1
  have atArrayN := carry.2.2.2.2.2.1
  have atRecordN := carry.2.2.2.2.2.2
  refine reaches_mono next (decodeHeaderAt 49) (decodeHeaderAt 50) _ _ _ _ (le_refl _) ?_
    (decode_header_excess_blobgas_field_keeps_state_root next array count input inputLength scratch frame record word
      ceiling inputLimit atArrayN atRecordN env.before env.recordFits tableN (by omega) env.above env.fits
      env.inputBound env.limitBound (env.scratchGlobalAt carry) (env.frameGlobalAt carry) (env.codeAt carry)
      env.orderedFrame env.framePositive env.scratchBelow (env.arenaAt carry) clock rootMem)
  intro post facts
  obtain ⟨root,dom,code,globals,table,atArray,atRecord,_⟩ := facts
  exact header_carry_intro s next post array count input inputLength record word carry root dom code globals table
    atArray atRecord

/-- `decodeHeaderAt 50 -> 52`: the excess-blob-gas word keeps the carry. -/
theorem header_carry_excess_blobgas_word {F : Type} (s next : PanSemStateFiniteExact 64 F)
    (array count input inputLength scratch frame record word : BitVec 64) (ceiling inputLimit : Nat)
    (env : HeaderCarryEnv s array count input inputLength scratch frame record ceiling inputLimit)
    (carry : HeaderSuffixCarry s next array count input inputLength record word)
    (clock : 1 * (headerRlpFieldCost inputLimit + 35) ≤ next.clock) :
    Reaches next (decodeHeaderAt 50)
      (fun post => HeaderSuffixCarry s post array count input inputLength record word)
      (1 * (headerRlpFieldCost inputLimit + 35)) (decodeHeaderAt 52) := by
  have countBound := env.countBound
  have rootMem := carry.1
  have domain := carry.2.1
  have codeEq := carry.2.2.1
  have globalsEq := carry.2.2.2.1
  have tableN := carry.2.2.2.2.1
  have atArrayN := carry.2.2.2.2.2.1
  have atRecordN := carry.2.2.2.2.2.2
  refine reaches_mono next (decodeHeaderAt 50) (decodeHeaderAt 52) _ _ _ _ (le_refl _) ?_
    (decode_header_excess_blobgas_keeps_state_root next array count input inputLength scratch frame record word ceiling
      inputLimit (by omega) atArrayN atRecordN env.before env.recordFits tableN env.above env.fits env.inputBound
      env.limitBound (env.scratchGlobalAt carry) (env.frameGlobalAt carry) (env.codeAt carry) env.orderedFrame
      env.framePositive env.scratchBelow (env.arenaAt carry) clock rootMem)
  intro post facts
  exact header_carry_of_word_frame s next post array count input inputLength record word ceiling carry facts

/-- `decodeHeaderAt 52 -> 56`: the last bytes fields keep the carry. -/
theorem header_carry_last_bytes {F : Type} (s next : PanSemStateFiniteExact 64 F)
    (array count input inputLength scratch frame record word : BitVec 64) (ceiling inputLimit : Nat)
    (env : HeaderCarryEnv s array count input inputLength scratch frame record ceiling inputLimit)
    (carry : HeaderSuffixCarry s next array count input inputLength record word)
    (clock : 2 * (headerRlpFieldCost inputLimit + 1) ≤ next.clock) :
    Reaches next (decodeHeaderAt 52)
      (fun post => HeaderSuffixCarry s post array count input inputLength record word)
      (2 * (headerRlpFieldCost inputLimit + 1)) (decodeHeaderAt 56) := by
  have countBound := env.countBound
  have rootMem := carry.1
  have domain := carry.2.1
  have codeEq := carry.2.2.1
  have globalsEq := carry.2.2.2.1
  have tableN := carry.2.2.2.2.1
  have atArrayN := carry.2.2.2.2.2.1
  have atRecordN := carry.2.2.2.2.2.2
  refine reaches_mono next (decodeHeaderAt 52) (decodeHeaderAt 56) _ _ _ _ (le_refl _) ?_
    (decode_header_last_bytes_keeps_state_root next array count input inputLength scratch frame record word ceiling
      inputLimit (by omega) atArrayN atRecordN env.before env.recordFits tableN env.above env.fits env.inputBound
      env.limitBound (env.scratchGlobalAt carry) (env.frameGlobalAt carry) (env.codeAt carry) env.orderedFrame
      env.framePositive env.scratchBelow (env.arenaAt carry) clock rootMem)
  intro post facts
  exact header_carry_of_bytes_frame s next post array count input inputLength record word ceiling carry facts

#print axioms header_carry_first_word
#print axioms header_carry_early_words
#print axioms header_carry_timestamp_field
#print axioms header_carry_timestamp_word
#print axioms header_carry_extra_field
#print axioms header_carry_middle_bytes
#print axioms header_carry_basefee
#print axioms header_carry_withdrawals_bytes
#print axioms header_carry_blobgas_field
#print axioms header_carry_blobgas_word
#print axioms header_carry_excess_blobgas_field
#print axioms header_carry_excess_blobgas_word
#print axioms header_carry_last_bytes
end InitECandidate.Runtime
