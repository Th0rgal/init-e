import InitECandidate.Runtime.HeaderCarryPhases
import InitECandidate.Runtime.DecodeHeaderFirstWordStateRootLocals
import InitECandidate.Runtime.DecodeHeaderTimestampFieldStateRootLocals
import InitECandidate.Runtime.DecodeHeaderBlobGasFieldStateRootLocals
import InitECandidate.Runtime.DecodeHeaderExcessBlobGasFieldStateRootLocals
import InitECandidate.Runtime.DecodeHeaderExtraFieldCarryLocals
import InitECandidate.Runtime.DecodeHeaderBasefeeCarryLocals
/-!
The carry chain keeps the `is_current` local.

`decodeHeaderAt 56` decides between the current and the legacy suffix by comparing the
local `is_current` with zero, so the suffix needs the value of that local in the state it
starts from.  A `Reaches` witness is only constrained by its predicate, so the value has
to be carried through the phases themselves rather than assumed: `HeaderCarryFlag` adds
the entry-independent fact `post.locals.lookup "is_current" = some (.val (.word flag))` to
`HeaderSuffixCarry`, and every one of the thirteen actual phases transports it.  The
frame-based phases get it from their frame's `locals` field, and the declaration-call
phases from the `_locals` carriers, whose declaration call resets only its own local.
-/
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
set_option maxRecDepth 100000
set_option maxHeartbeats 400000

/-- The suffix carry together with the `is_current` local that decides the suffix. -/
def HeaderCarryFlag {F : Type} (s post : PanSemStateFiniteExact 64 F)
    (array count input inputLength record word flag : BitVec 64) : Prop :=
  HeaderSuffixCarry s post array count input inputLength record word ∧
    post.locals.lookup (ofString "is_current") = some (.val (.word flag))


/-- `decodeHeaderAt 25 -> 27`: the first word field keeps the carry. -/
theorem header_carry_flag_first_word {F : Type} (s next : PanSemStateFiniteExact 64 F)
    (array count input inputLength scratch frame record word flag : BitVec 64) (ceiling inputLimit : Nat)
    (env : HeaderCarryEnv s array count input inputLength scratch frame record ceiling inputLimit)
    (carried : HeaderCarryFlag s next array count input inputLength record word flag)
    (atFlag : next.locals.lookup (ofString "is_current") = some (.val (.word flag)))
    (clock : headerRlpFieldCost inputLimit + 35 ≤ next.clock) :
    Reaches next (decodeHeaderAt 25)
      (fun post => HeaderCarryFlag s post array count input inputLength record word flag)
      (headerRlpFieldCost inputLimit + 35) (decodeHeaderAt 27) := by
  have carry := carried.1
  have countBound := env.countBound
  have rootMem := carry.1
  have domain := carry.2.1
  have codeEq := carry.2.2.1
  have globalsEq := carry.2.2.2.1
  have tableN := carry.2.2.2.2.1
  have atArrayN := carry.2.2.2.2.2.1
  have atRecordN := carry.2.2.2.2.2.2
  refine reaches_mono next (decodeHeaderAt 25) (decodeHeaderAt 27) _ _ _ _ (le_refl _) ?_
    (decode_header_first_word_keeps_state_root_locals next array count input inputLength scratch frame record word ceiling
      inputLimit (by omega) atArrayN atRecordN env.before env.recordFits tableN env.above env.fits env.inputBound
      env.limitBound (env.scratchGlobalAt carry) (env.frameGlobalAt carry) (env.codeAt carry) env.orderedFrame
      env.framePositive env.scratchBelow (env.arenaAt carry) clock rootMem)
  intro post facts
  obtain ⟨root,dom,code,globals,table,atArray,atRecord,_,flagKept⟩ := facts
  exact ⟨header_carry_intro s next post array count input inputLength record word carry root dom code globals table
    atArray atRecord,(flagKept).trans atFlag⟩

/-- `decodeHeaderAt 27 -> 31`: the two early word fields keep the carry. -/
theorem header_carry_flag_early_words {F : Type} (s next : PanSemStateFiniteExact 64 F)
    (array count input inputLength scratch frame record word flag : BitVec 64) (ceiling inputLimit : Nat)
    (env : HeaderCarryEnv s array count input inputLength scratch frame record ceiling inputLimit)
    (carried : HeaderCarryFlag s next array count input inputLength record word flag)
    (atFlag : next.locals.lookup (ofString "is_current") = some (.val (.word flag)))
    (clock : 2 * (headerRlpFieldCost inputLimit + 35) ≤ next.clock) :
    Reaches next (decodeHeaderAt 27)
      (fun post => HeaderCarryFlag s post array count input inputLength record word flag)
      (2 * (headerRlpFieldCost inputLimit + 35)) (decodeHeaderAt 31) := by
  have carry := carried.1
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
  exact ⟨header_carry_of_word_frame s next post array count input inputLength record word ceiling carry facts,
    (facts.2.locals (ofString "is_current") (by decide)).trans atFlag⟩

/-- `decodeHeaderAt 31 -> 33`: the timestamp field and its width guard keep the carry. -/
theorem header_carry_flag_timestamp_field {F : Type} (s next : PanSemStateFiniteExact 64 F)
    (array count input inputLength scratch frame record word flag : BitVec 64) (ceiling inputLimit : Nat)
    (env : HeaderCarryEnv s array count input inputLength scratch frame record ceiling inputLimit)
    (carried : HeaderCarryFlag s next array count input inputLength record word flag)
    (atFlag : next.locals.lookup (ofString "is_current") = some (.val (.word flag)))
    (clock : headerRlpFieldCost inputLimit + 1 ≤ next.clock) :
    Reaches next (decodeHeaderAt 31)
      (fun post => HeaderCarryFlag s post array count input inputLength record word flag)
      (headerRlpFieldCost inputLimit + 1) (decodeHeaderAt 33) := by
  have carry := carried.1
  have countBound := env.countBound
  have rootMem := carry.1
  have domain := carry.2.1
  have codeEq := carry.2.2.1
  have globalsEq := carry.2.2.2.1
  have tableN := carry.2.2.2.2.1
  have atArrayN := carry.2.2.2.2.2.1
  have atRecordN := carry.2.2.2.2.2.2
  refine reaches_mono next (decodeHeaderAt 31) (decodeHeaderAt 33) _ _ _ _ (le_refl _) ?_
    (decode_header_timestamp_field_keeps_state_root_locals next array count input inputLength scratch frame record word ceiling
      inputLimit atArrayN atRecordN env.before env.recordFits tableN (by omega) env.above env.fits env.inputBound
      env.limitBound (env.scratchGlobalAt carry) (env.frameGlobalAt carry) (env.codeAt carry) env.orderedFrame
      env.framePositive env.scratchBelow (env.arenaAt carry) clock rootMem)
  intro post facts
  obtain ⟨root,dom,code,globals,table,atArray,atRecord,_,flagKept⟩ := facts
  exact ⟨header_carry_intro s next post array count input inputLength record word carry root dom code globals table
    atArray atRecord,(flagKept).trans atFlag⟩

/-- `decodeHeaderAt 33 -> 35`: the timestamp word keeps the carry. -/
theorem header_carry_flag_timestamp_word {F : Type} (s next : PanSemStateFiniteExact 64 F)
    (array count input inputLength scratch frame record word flag : BitVec 64) (ceiling inputLimit : Nat)
    (env : HeaderCarryEnv s array count input inputLength scratch frame record ceiling inputLimit)
    (carried : HeaderCarryFlag s next array count input inputLength record word flag)
    (atFlag : next.locals.lookup (ofString "is_current") = some (.val (.word flag)))
    (clock : 1 * (headerRlpFieldCost inputLimit + 35) ≤ next.clock) :
    Reaches next (decodeHeaderAt 33)
      (fun post => HeaderCarryFlag s post array count input inputLength record word flag)
      (1 * (headerRlpFieldCost inputLimit + 35)) (decodeHeaderAt 35) := by
  have carry := carried.1
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
  exact ⟨header_carry_of_word_frame s next post array count input inputLength record word ceiling carry facts,
    (facts.2.locals (ofString "is_current") (by decide)).trans atFlag⟩

/-- `decodeHeaderAt 35 -> 38`: the extra-data field and its two stores keep the carry. -/
theorem header_carry_flag_extra_field {F : Type} (s next : PanSemStateFiniteExact 64 F)
    (array count input inputLength scratch frame record word flag : BitVec 64) (ceiling inputLimit : Nat)
    (env : HeaderCarryEnv s array count input inputLength scratch frame record ceiling inputLimit)
    (carried : HeaderCarryFlag s next array count input inputLength record word flag)
    (atFlag : next.locals.lookup (ofString "is_current") = some (.val (.word flag)))
    (clock : headerRlpFieldCost inputLimit + 1 ≤ next.clock) :
    Reaches next (decodeHeaderAt 35)
      (fun post => HeaderCarryFlag s post array count input inputLength record word flag)
      (headerRlpFieldCost inputLimit + 1) (decodeHeaderAt 38) := by
  have carry := carried.1
  have countBound := env.countBound
  have rootMem := carry.1
  have domain := carry.2.1
  have codeEq := carry.2.2.1
  have globalsEq := carry.2.2.2.1
  have tableN := carry.2.2.2.2.1
  have atArrayN := carry.2.2.2.2.2.1
  have atRecordN := carry.2.2.2.2.2.2
  refine reaches_mono next (decodeHeaderAt 35) (decodeHeaderAt 38) _ _ _ _ (le_refl _) ?_
    (decode_header_extra_field_ready_locals next array count input inputLength scratch frame record word ceiling
      inputLimit atArrayN atRecordN env.before env.recordFits tableN (by omega) env.above env.fits env.inputBound
      env.limitBound (env.scratchGlobalAt carry) (env.frameGlobalAt carry) (env.codeAt carry) env.orderedFrame
      env.framePositive env.scratchBelow (env.arenaAt carry) clock rootMem)
  intro post facts
  obtain ⟨root,dom,code,globals,table,atArray,atRecord,flagKept⟩ := facts
  exact ⟨header_carry_intro s next post array count input inputLength record word carry root dom code globals table
    atArray atRecord,(flagKept).trans atFlag⟩

/-- `decodeHeaderAt 38 -> 42`: the middle bytes fields keep the carry. -/
theorem header_carry_flag_middle_bytes {F : Type} (s next : PanSemStateFiniteExact 64 F)
    (array count input inputLength scratch frame record word flag : BitVec 64) (ceiling inputLimit : Nat)
    (env : HeaderCarryEnv s array count input inputLength scratch frame record ceiling inputLimit)
    (carried : HeaderCarryFlag s next array count input inputLength record word flag)
    (atFlag : next.locals.lookup (ofString "is_current") = some (.val (.word flag)))
    (clock : 2 * (headerRlpFieldCost inputLimit + 1) ≤ next.clock) :
    Reaches next (decodeHeaderAt 38)
      (fun post => HeaderCarryFlag s post array count input inputLength record word flag)
      (2 * (headerRlpFieldCost inputLimit + 1)) (decodeHeaderAt 42) := by
  have carry := carried.1
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
  exact ⟨header_carry_of_bytes_frame s next post array count input inputLength record word ceiling carry facts,
    (facts.2.locals (ofString "is_current") (by decide)).trans atFlag⟩

/-- `decodeHeaderAt 42 -> 44`: the base-fee field and its four-limb store keep the carry. -/
theorem header_carry_flag_basefee {F : Type} (s next : PanSemStateFiniteExact 64 F)
    (array count input inputLength scratch frame record word flag : BitVec 64) (ceiling inputLimit : Nat)
    (env : HeaderCarryEnv s array count input inputLength scratch frame record ceiling inputLimit)
    (carried : HeaderCarryFlag s next array count input inputLength record word flag)
    (atFlag : next.locals.lookup (ofString "is_current") = some (.val (.word flag)))
    (clock : headerRlpFieldCost inputLimit + 35 ≤ next.clock) :
    Reaches next (decodeHeaderAt 42)
      (fun post => HeaderCarryFlag s post array count input inputLength record word flag)
      (headerRlpFieldCost inputLimit + 35) (decodeHeaderAt 44) := by
  have carry := carried.1
  have countBound := env.countBound
  have rootMem := carry.1
  have domain := carry.2.1
  have codeEq := carry.2.2.1
  have globalsEq := carry.2.2.2.1
  have tableN := carry.2.2.2.2.1
  have atArrayN := carry.2.2.2.2.2.1
  have atRecordN := carry.2.2.2.2.2.2
  refine reaches_mono next (decodeHeaderAt 42) (decodeHeaderAt 44) _ _ _ _ (le_refl _) ?_
    (decode_header_basefee_ready_locals next array count input inputLength scratch frame record word ceiling
      inputLimit atArrayN atRecordN env.before env.recordFits tableN (by omega) env.above env.fits env.inputBound
      env.limitBound (env.scratchGlobalAt carry) (env.frameGlobalAt carry) (env.codeAt carry) env.orderedFrame
      env.framePositive env.scratchBelow (env.arenaAt carry) clock rootMem)
  intro post facts
  obtain ⟨root,dom,code,globals,table,atArray,atRecord,flagKept⟩ := facts
  exact ⟨header_carry_intro s next post array count input inputLength record word carry root dom code globals table
    atArray atRecord,(flagKept).trans atFlag⟩

/-- `decodeHeaderAt 44 -> 46`: the withdrawals-root field keeps the carry. -/
theorem header_carry_flag_withdrawals_bytes {F : Type} (s next : PanSemStateFiniteExact 64 F)
    (array count input inputLength scratch frame record word flag : BitVec 64) (ceiling inputLimit : Nat)
    (env : HeaderCarryEnv s array count input inputLength scratch frame record ceiling inputLimit)
    (carried : HeaderCarryFlag s next array count input inputLength record word flag)
    (atFlag : next.locals.lookup (ofString "is_current") = some (.val (.word flag)))
    (clock : 1 * (headerRlpFieldCost inputLimit + 1) ≤ next.clock) :
    Reaches next (decodeHeaderAt 44)
      (fun post => HeaderCarryFlag s post array count input inputLength record word flag)
      (1 * (headerRlpFieldCost inputLimit + 1)) (decodeHeaderAt 46) := by
  have carry := carried.1
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
  exact ⟨header_carry_of_bytes_frame s next post array count input inputLength record word ceiling carry facts,
    (facts.2.locals (ofString "is_current") (by decide)).trans atFlag⟩

/-- `decodeHeaderAt 46 -> 47`: the blob-gas field keeps the carry. -/
theorem header_carry_flag_blobgas_field {F : Type} (s next : PanSemStateFiniteExact 64 F)
    (array count input inputLength scratch frame record word flag : BitVec 64) (ceiling inputLimit : Nat)
    (env : HeaderCarryEnv s array count input inputLength scratch frame record ceiling inputLimit)
    (carried : HeaderCarryFlag s next array count input inputLength record word flag)
    (atFlag : next.locals.lookup (ofString "is_current") = some (.val (.word flag)))
    (clock : headerRlpFieldCost inputLimit + 1 ≤ next.clock) :
    Reaches next (decodeHeaderAt 46)
      (fun post => HeaderCarryFlag s post array count input inputLength record word flag)
      (headerRlpFieldCost inputLimit + 1) (decodeHeaderAt 47) := by
  have carry := carried.1
  have countBound := env.countBound
  have rootMem := carry.1
  have domain := carry.2.1
  have codeEq := carry.2.2.1
  have globalsEq := carry.2.2.2.1
  have tableN := carry.2.2.2.2.1
  have atArrayN := carry.2.2.2.2.2.1
  have atRecordN := carry.2.2.2.2.2.2
  refine reaches_mono next (decodeHeaderAt 46) (decodeHeaderAt 47) _ _ _ _ (le_refl _) ?_
    (decode_header_blobgas_field_keeps_state_root_locals next array count input inputLength scratch frame record word ceiling
      inputLimit atArrayN atRecordN env.before env.recordFits tableN (by omega) env.above env.fits env.inputBound
      env.limitBound (env.scratchGlobalAt carry) (env.frameGlobalAt carry) (env.codeAt carry) env.orderedFrame
      env.framePositive env.scratchBelow (env.arenaAt carry) clock rootMem)
  intro post facts
  obtain ⟨root,dom,code,globals,table,atArray,atRecord,_,flagKept⟩ := facts
  exact ⟨header_carry_intro s next post array count input inputLength record word carry root dom code globals table
    atArray atRecord,(flagKept).trans atFlag⟩

/-- `decodeHeaderAt 47 -> 49`: the blob-gas word keeps the carry. -/
theorem header_carry_flag_blobgas_word {F : Type} (s next : PanSemStateFiniteExact 64 F)
    (array count input inputLength scratch frame record word flag : BitVec 64) (ceiling inputLimit : Nat)
    (env : HeaderCarryEnv s array count input inputLength scratch frame record ceiling inputLimit)
    (carried : HeaderCarryFlag s next array count input inputLength record word flag)
    (atFlag : next.locals.lookup (ofString "is_current") = some (.val (.word flag)))
    (clock : 1 * (headerRlpFieldCost inputLimit + 35) ≤ next.clock) :
    Reaches next (decodeHeaderAt 47)
      (fun post => HeaderCarryFlag s post array count input inputLength record word flag)
      (1 * (headerRlpFieldCost inputLimit + 35)) (decodeHeaderAt 49) := by
  have carry := carried.1
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
  exact ⟨header_carry_of_word_frame s next post array count input inputLength record word ceiling carry facts,
    (facts.2.locals (ofString "is_current") (by decide)).trans atFlag⟩

/-- `decodeHeaderAt 49 -> 50`: the excess-blob-gas field keeps the carry. -/
theorem header_carry_flag_excess_blobgas_field {F : Type} (s next : PanSemStateFiniteExact 64 F)
    (array count input inputLength scratch frame record word flag : BitVec 64) (ceiling inputLimit : Nat)
    (env : HeaderCarryEnv s array count input inputLength scratch frame record ceiling inputLimit)
    (carried : HeaderCarryFlag s next array count input inputLength record word flag)
    (atFlag : next.locals.lookup (ofString "is_current") = some (.val (.word flag)))
    (clock : headerRlpFieldCost inputLimit + 1 ≤ next.clock) :
    Reaches next (decodeHeaderAt 49)
      (fun post => HeaderCarryFlag s post array count input inputLength record word flag)
      (headerRlpFieldCost inputLimit + 1) (decodeHeaderAt 50) := by
  have carry := carried.1
  have countBound := env.countBound
  have rootMem := carry.1
  have domain := carry.2.1
  have codeEq := carry.2.2.1
  have globalsEq := carry.2.2.2.1
  have tableN := carry.2.2.2.2.1
  have atArrayN := carry.2.2.2.2.2.1
  have atRecordN := carry.2.2.2.2.2.2
  refine reaches_mono next (decodeHeaderAt 49) (decodeHeaderAt 50) _ _ _ _ (le_refl _) ?_
    (decode_header_excess_blobgas_field_keeps_state_root_locals next array count input inputLength scratch frame record word
      ceiling inputLimit atArrayN atRecordN env.before env.recordFits tableN (by omega) env.above env.fits
      env.inputBound env.limitBound (env.scratchGlobalAt carry) (env.frameGlobalAt carry) (env.codeAt carry)
      env.orderedFrame env.framePositive env.scratchBelow (env.arenaAt carry) clock rootMem)
  intro post facts
  obtain ⟨root,dom,code,globals,table,atArray,atRecord,_,flagKept⟩ := facts
  exact ⟨header_carry_intro s next post array count input inputLength record word carry root dom code globals table
    atArray atRecord,(flagKept).trans atFlag⟩

/-- `decodeHeaderAt 50 -> 52`: the excess-blob-gas word keeps the carry. -/
theorem header_carry_flag_excess_blobgas_word {F : Type} (s next : PanSemStateFiniteExact 64 F)
    (array count input inputLength scratch frame record word flag : BitVec 64) (ceiling inputLimit : Nat)
    (env : HeaderCarryEnv s array count input inputLength scratch frame record ceiling inputLimit)
    (carried : HeaderCarryFlag s next array count input inputLength record word flag)
    (atFlag : next.locals.lookup (ofString "is_current") = some (.val (.word flag)))
    (clock : 1 * (headerRlpFieldCost inputLimit + 35) ≤ next.clock) :
    Reaches next (decodeHeaderAt 50)
      (fun post => HeaderCarryFlag s post array count input inputLength record word flag)
      (1 * (headerRlpFieldCost inputLimit + 35)) (decodeHeaderAt 52) := by
  have carry := carried.1
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
  exact ⟨header_carry_of_word_frame s next post array count input inputLength record word ceiling carry facts,
    (facts.2.locals (ofString "is_current") (by decide)).trans atFlag⟩

/-- `decodeHeaderAt 52 -> 56`: the last bytes fields keep the carry. -/
theorem header_carry_flag_last_bytes {F : Type} (s next : PanSemStateFiniteExact 64 F)
    (array count input inputLength scratch frame record word flag : BitVec 64) (ceiling inputLimit : Nat)
    (env : HeaderCarryEnv s array count input inputLength scratch frame record ceiling inputLimit)
    (carried : HeaderCarryFlag s next array count input inputLength record word flag)
    (atFlag : next.locals.lookup (ofString "is_current") = some (.val (.word flag)))
    (clock : 2 * (headerRlpFieldCost inputLimit + 1) ≤ next.clock) :
    Reaches next (decodeHeaderAt 52)
      (fun post => HeaderCarryFlag s post array count input inputLength record word flag)
      (2 * (headerRlpFieldCost inputLimit + 1)) (decodeHeaderAt 56) := by
  have carry := carried.1
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
  exact ⟨header_carry_of_bytes_frame s next post array count input inputLength record word ceiling carry facts,
    (facts.2.locals (ofString "is_current") (by decide)).trans atFlag⟩

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
