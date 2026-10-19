import InitECandidate.Runtime.DecodeHeaderFlagChain
import InitECandidate.Runtime.DecodeHeaderWholeCarry
import InitECandidate.Runtime.DecodeHeaderReturnedRoot
/-!
The whole actual header decoder, keeping the `is_current` value that decides the suffix.

`decodeHeaderAt 56` compares the local `is_current` with zero, and the suffix phase
`header_carry_suffix` needs that local in the state it starts from.  A `Reaches` witness is
only constrained by its predicate, so the value has to be transported by the run itself:
`HeaderCarryFlag` pairs the carry with it, and this module carries it from
`decodeHeaderAt 11` — through the early bytes chain, the difficulty phase and all thirteen
field phases — to `decodeHeaderAt 56`, then through the actual current/legacy suffix to
`decodeHeaderAt 57`.

That closes the returned-header contract for both header kinds: a 21-field legacy header
has `is_current = 0` and runs the legacy suffix, a 23-field current header has
`is_current = 1` and runs the current suffix, which needs entry 22 and hence 23 fields.
Both cases only need the zero-test invariant `is_current ≠ 0 → 23 ≤ count`.
-/
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
set_option maxRecDepth 100000
set_option maxHeartbeats 800000

/-- The same span entered at any state that already carries the reference state's carry
and `is_current` value: the thirteen actual phases keep both. -/
theorem decode_header_flag_span_from {F : Type} (s next : PanSemStateFiniteExact 64 F)
    (array count input inputLength scratch frame record word : BitVec 64)  (ceiling inputLimit : Nat)
    (env : HeaderCarryEnv s array count input inputLength scratch frame record ceiling inputLimit)
    (flag : BitVec 64)
    (entry : HeaderCarryFlag s next array count input inputLength record word flag)
    (budget : headerDecoderSpanCost inputLimit ≤ next.clock) :
    Reaches next (decodeHeaderAt 25)
      (fun post => HeaderCarryFlag s post array count input inputLength record word flag)
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
  have stage1 : Reaches next (decodeHeaderAt 25) (fun post => HeaderCarryFlag s post array count input inputLength record word flag) (headerRlpFieldCost inputLimit + 35) (decodeHeaderAt 27) :=
    header_carry_flag_first_word s next array count input inputLength scratch frame record word flag ceiling inputLimit env entry entry.2 (by omega)
  have stage2 : Reaches next (decodeHeaderAt 25) (fun post => HeaderCarryFlag s post array count input inputLength record word flag)
      ((headerRlpFieldCost inputLimit + 35) + 2 * (headerRlpFieldCost inputLimit + 35))      (decodeHeaderAt 31) :=
    reaches_trans_budget next (decodeHeaderAt 25) (decodeHeaderAt 27) (decodeHeaderAt 31) (fun post => HeaderCarryFlag s post array count input inputLength record word flag)
      (fun post => HeaderCarryFlag s post array count input inputLength record word flag)
      ((headerRlpFieldCost inputLimit + 35)) (2 * (headerRlpFieldCost inputLimit + 35)) (by omega) stage1
      (fun next carried clock => header_carry_flag_early_words s next array count input inputLength scratch frame record word flag ceiling inputLimit env carried carried.2 clock)
  have stage3 : Reaches next (decodeHeaderAt 25) (fun post => HeaderCarryFlag s post array count input inputLength record word flag)
      ((headerRlpFieldCost inputLimit + 35) + 2 * (headerRlpFieldCost inputLimit + 35) +
        (headerRlpFieldCost inputLimit + 1))      (decodeHeaderAt 33) :=
    reaches_trans_budget next (decodeHeaderAt 25) (decodeHeaderAt 31) (decodeHeaderAt 33) (fun post => HeaderCarryFlag s post array count input inputLength record word flag)
      (fun post => HeaderCarryFlag s post array count input inputLength record word flag)
      ((headerRlpFieldCost inputLimit + 35) + 2 * (headerRlpFieldCost inputLimit + 35)) ((headerRlpFieldCost inputLimit + 1)) (by omega) stage2
      (fun next carried clock => header_carry_flag_timestamp_field s next array count input inputLength scratch frame record word flag ceiling inputLimit env carried carried.2 clock)
  have stage4 : Reaches next (decodeHeaderAt 25) (fun post => HeaderCarryFlag s post array count input inputLength record word flag)
      ((headerRlpFieldCost inputLimit + 35) + 2 * (headerRlpFieldCost inputLimit + 35) +
        (headerRlpFieldCost inputLimit + 1) + 1 * (headerRlpFieldCost inputLimit + 35))      (decodeHeaderAt 35) :=
    reaches_trans_budget next (decodeHeaderAt 25) (decodeHeaderAt 33) (decodeHeaderAt 35) (fun post => HeaderCarryFlag s post array count input inputLength record word flag)
      (fun post => HeaderCarryFlag s post array count input inputLength record word flag)
      ((headerRlpFieldCost inputLimit + 35) + 2 * (headerRlpFieldCost inputLimit + 35) +
        (headerRlpFieldCost inputLimit + 1)) (1 * (headerRlpFieldCost inputLimit + 35)) (by omega) stage3
      (fun next carried clock => header_carry_flag_timestamp_word s next array count input inputLength scratch frame record word flag ceiling inputLimit env carried carried.2 clock)
  have stage5 : Reaches next (decodeHeaderAt 25) (fun post => HeaderCarryFlag s post array count input inputLength record word flag)
      ((headerRlpFieldCost inputLimit + 35) + 2 * (headerRlpFieldCost inputLimit + 35) +
        (headerRlpFieldCost inputLimit + 1) + 1 * (headerRlpFieldCost inputLimit + 35) +
        (headerRlpFieldCost inputLimit + 1))      (decodeHeaderAt 38) :=
    reaches_trans_budget next (decodeHeaderAt 25) (decodeHeaderAt 35) (decodeHeaderAt 38) (fun post => HeaderCarryFlag s post array count input inputLength record word flag)
      (fun post => HeaderCarryFlag s post array count input inputLength record word flag)
      ((headerRlpFieldCost inputLimit + 35) + 2 * (headerRlpFieldCost inputLimit + 35) +
        (headerRlpFieldCost inputLimit + 1) + 1 * (headerRlpFieldCost inputLimit + 35)) ((headerRlpFieldCost inputLimit + 1)) (by omega) stage4
      (fun next carried clock => header_carry_flag_extra_field s next array count input inputLength scratch frame record word flag ceiling inputLimit env carried carried.2 clock)
  have stage6 : Reaches next (decodeHeaderAt 25) (fun post => HeaderCarryFlag s post array count input inputLength record word flag)
      ((headerRlpFieldCost inputLimit + 35) + 2 * (headerRlpFieldCost inputLimit + 35) +
        (headerRlpFieldCost inputLimit + 1) + 1 * (headerRlpFieldCost inputLimit + 35) +
        (headerRlpFieldCost inputLimit + 1) + 2 * (headerRlpFieldCost inputLimit + 1))      (decodeHeaderAt 42) :=
    reaches_trans_budget next (decodeHeaderAt 25) (decodeHeaderAt 38) (decodeHeaderAt 42) (fun post => HeaderCarryFlag s post array count input inputLength record word flag)
      (fun post => HeaderCarryFlag s post array count input inputLength record word flag)
      ((headerRlpFieldCost inputLimit + 35) + 2 * (headerRlpFieldCost inputLimit + 35) +
        (headerRlpFieldCost inputLimit + 1) + 1 * (headerRlpFieldCost inputLimit + 35) +
        (headerRlpFieldCost inputLimit + 1)) (2 * (headerRlpFieldCost inputLimit + 1)) (by omega) stage5
      (fun next carried clock => header_carry_flag_middle_bytes s next array count input inputLength scratch frame record word flag ceiling inputLimit env carried carried.2 clock)
  have stage7 : Reaches next (decodeHeaderAt 25) (fun post => HeaderCarryFlag s post array count input inputLength record word flag)
      ((headerRlpFieldCost inputLimit + 35) + 2 * (headerRlpFieldCost inputLimit + 35) +
        (headerRlpFieldCost inputLimit + 1) + 1 * (headerRlpFieldCost inputLimit + 35) +
        (headerRlpFieldCost inputLimit + 1) + 2 * (headerRlpFieldCost inputLimit + 1) +
        (headerRlpFieldCost inputLimit + 35))      (decodeHeaderAt 44) :=
    reaches_trans_budget next (decodeHeaderAt 25) (decodeHeaderAt 42) (decodeHeaderAt 44) (fun post => HeaderCarryFlag s post array count input inputLength record word flag)
      (fun post => HeaderCarryFlag s post array count input inputLength record word flag)
      ((headerRlpFieldCost inputLimit + 35) + 2 * (headerRlpFieldCost inputLimit + 35) +
        (headerRlpFieldCost inputLimit + 1) + 1 * (headerRlpFieldCost inputLimit + 35) +
        (headerRlpFieldCost inputLimit + 1) + 2 * (headerRlpFieldCost inputLimit + 1)) ((headerRlpFieldCost inputLimit + 35)) (by omega) stage6
      (fun next carried clock => header_carry_flag_basefee s next array count input inputLength scratch frame record word flag ceiling inputLimit env carried carried.2 clock)
  have stage8 : Reaches next (decodeHeaderAt 25) (fun post => HeaderCarryFlag s post array count input inputLength record word flag)
      ((headerRlpFieldCost inputLimit + 35) + 2 * (headerRlpFieldCost inputLimit + 35) +
        (headerRlpFieldCost inputLimit + 1) + 1 * (headerRlpFieldCost inputLimit + 35) +
        (headerRlpFieldCost inputLimit + 1) + 2 * (headerRlpFieldCost inputLimit + 1) +
        (headerRlpFieldCost inputLimit + 35) + 1 * (headerRlpFieldCost inputLimit + 1))      (decodeHeaderAt 46) :=
    reaches_trans_budget next (decodeHeaderAt 25) (decodeHeaderAt 44) (decodeHeaderAt 46) (fun post => HeaderCarryFlag s post array count input inputLength record word flag)
      (fun post => HeaderCarryFlag s post array count input inputLength record word flag)
      ((headerRlpFieldCost inputLimit + 35) + 2 * (headerRlpFieldCost inputLimit + 35) +
        (headerRlpFieldCost inputLimit + 1) + 1 * (headerRlpFieldCost inputLimit + 35) +
        (headerRlpFieldCost inputLimit + 1) + 2 * (headerRlpFieldCost inputLimit + 1) +
        (headerRlpFieldCost inputLimit + 35)) (1 * (headerRlpFieldCost inputLimit + 1)) (by omega) stage7
      (fun next carried clock => header_carry_flag_withdrawals_bytes s next array count input inputLength scratch frame record word flag ceiling inputLimit env carried carried.2 clock)
  have stage9 : Reaches next (decodeHeaderAt 25) (fun post => HeaderCarryFlag s post array count input inputLength record word flag)
      ((headerRlpFieldCost inputLimit + 35) + 2 * (headerRlpFieldCost inputLimit + 35) +
        (headerRlpFieldCost inputLimit + 1) + 1 * (headerRlpFieldCost inputLimit + 35) +
        (headerRlpFieldCost inputLimit + 1) + 2 * (headerRlpFieldCost inputLimit + 1) +
        (headerRlpFieldCost inputLimit + 35) + 1 * (headerRlpFieldCost inputLimit + 1) +
        (headerRlpFieldCost inputLimit + 1))      (decodeHeaderAt 47) :=
    reaches_trans_budget next (decodeHeaderAt 25) (decodeHeaderAt 46) (decodeHeaderAt 47) (fun post => HeaderCarryFlag s post array count input inputLength record word flag)
      (fun post => HeaderCarryFlag s post array count input inputLength record word flag)
      ((headerRlpFieldCost inputLimit + 35) + 2 * (headerRlpFieldCost inputLimit + 35) +
        (headerRlpFieldCost inputLimit + 1) + 1 * (headerRlpFieldCost inputLimit + 35) +
        (headerRlpFieldCost inputLimit + 1) + 2 * (headerRlpFieldCost inputLimit + 1) +
        (headerRlpFieldCost inputLimit + 35) + 1 * (headerRlpFieldCost inputLimit + 1)) ((headerRlpFieldCost inputLimit + 1)) (by omega) stage8
      (fun next carried clock => header_carry_flag_blobgas_field s next array count input inputLength scratch frame record word flag ceiling inputLimit env carried carried.2 clock)
  have stage10 : Reaches next (decodeHeaderAt 25) (fun post => HeaderCarryFlag s post array count input inputLength record word flag)
      ((headerRlpFieldCost inputLimit + 35) + 2 * (headerRlpFieldCost inputLimit + 35) +
        (headerRlpFieldCost inputLimit + 1) + 1 * (headerRlpFieldCost inputLimit + 35) +
        (headerRlpFieldCost inputLimit + 1) + 2 * (headerRlpFieldCost inputLimit + 1) +
        (headerRlpFieldCost inputLimit + 35) + 1 * (headerRlpFieldCost inputLimit + 1) +
        (headerRlpFieldCost inputLimit + 1) + 1 * (headerRlpFieldCost inputLimit + 35))      (decodeHeaderAt 49) :=
    reaches_trans_budget next (decodeHeaderAt 25) (decodeHeaderAt 47) (decodeHeaderAt 49) (fun post => HeaderCarryFlag s post array count input inputLength record word flag)
      (fun post => HeaderCarryFlag s post array count input inputLength record word flag)
      ((headerRlpFieldCost inputLimit + 35) + 2 * (headerRlpFieldCost inputLimit + 35) +
        (headerRlpFieldCost inputLimit + 1) + 1 * (headerRlpFieldCost inputLimit + 35) +
        (headerRlpFieldCost inputLimit + 1) + 2 * (headerRlpFieldCost inputLimit + 1) +
        (headerRlpFieldCost inputLimit + 35) + 1 * (headerRlpFieldCost inputLimit + 1) +
        (headerRlpFieldCost inputLimit + 1)) (1 * (headerRlpFieldCost inputLimit + 35)) (by omega) stage9
      (fun next carried clock => header_carry_flag_blobgas_word s next array count input inputLength scratch frame record word flag ceiling inputLimit env carried carried.2 clock)
  have stage11 : Reaches next (decodeHeaderAt 25) (fun post => HeaderCarryFlag s post array count input inputLength record word flag)
      ((headerRlpFieldCost inputLimit + 35) + 2 * (headerRlpFieldCost inputLimit + 35) +
        (headerRlpFieldCost inputLimit + 1) + 1 * (headerRlpFieldCost inputLimit + 35) +
        (headerRlpFieldCost inputLimit + 1) + 2 * (headerRlpFieldCost inputLimit + 1) +
        (headerRlpFieldCost inputLimit + 35) + 1 * (headerRlpFieldCost inputLimit + 1) +
        (headerRlpFieldCost inputLimit + 1) + 1 * (headerRlpFieldCost inputLimit + 35) +
        (headerRlpFieldCost inputLimit + 1))      (decodeHeaderAt 50) :=
    reaches_trans_budget next (decodeHeaderAt 25) (decodeHeaderAt 49) (decodeHeaderAt 50) (fun post => HeaderCarryFlag s post array count input inputLength record word flag)
      (fun post => HeaderCarryFlag s post array count input inputLength record word flag)
      ((headerRlpFieldCost inputLimit + 35) + 2 * (headerRlpFieldCost inputLimit + 35) +
        (headerRlpFieldCost inputLimit + 1) + 1 * (headerRlpFieldCost inputLimit + 35) +
        (headerRlpFieldCost inputLimit + 1) + 2 * (headerRlpFieldCost inputLimit + 1) +
        (headerRlpFieldCost inputLimit + 35) + 1 * (headerRlpFieldCost inputLimit + 1) +
        (headerRlpFieldCost inputLimit + 1) + 1 * (headerRlpFieldCost inputLimit + 35)) ((headerRlpFieldCost inputLimit + 1)) (by omega) stage10
      (fun next carried clock => header_carry_flag_excess_blobgas_field s next array count input inputLength scratch frame record word flag ceiling inputLimit env carried carried.2 clock)
  have stage12 : Reaches next (decodeHeaderAt 25) (fun post => HeaderCarryFlag s post array count input inputLength record word flag)
      ((headerRlpFieldCost inputLimit + 35) + 2 * (headerRlpFieldCost inputLimit + 35) +
        (headerRlpFieldCost inputLimit + 1) + 1 * (headerRlpFieldCost inputLimit + 35) +
        (headerRlpFieldCost inputLimit + 1) + 2 * (headerRlpFieldCost inputLimit + 1) +
        (headerRlpFieldCost inputLimit + 35) + 1 * (headerRlpFieldCost inputLimit + 1) +
        (headerRlpFieldCost inputLimit + 1) + 1 * (headerRlpFieldCost inputLimit + 35) +
        (headerRlpFieldCost inputLimit + 1) + 1 * (headerRlpFieldCost inputLimit + 35))      (decodeHeaderAt 52) :=
    reaches_trans_budget next (decodeHeaderAt 25) (decodeHeaderAt 50) (decodeHeaderAt 52) (fun post => HeaderCarryFlag s post array count input inputLength record word flag)
      (fun post => HeaderCarryFlag s post array count input inputLength record word flag)
      ((headerRlpFieldCost inputLimit + 35) + 2 * (headerRlpFieldCost inputLimit + 35) +
        (headerRlpFieldCost inputLimit + 1) + 1 * (headerRlpFieldCost inputLimit + 35) +
        (headerRlpFieldCost inputLimit + 1) + 2 * (headerRlpFieldCost inputLimit + 1) +
        (headerRlpFieldCost inputLimit + 35) + 1 * (headerRlpFieldCost inputLimit + 1) +
        (headerRlpFieldCost inputLimit + 1) + 1 * (headerRlpFieldCost inputLimit + 35) +
        (headerRlpFieldCost inputLimit + 1)) (1 * (headerRlpFieldCost inputLimit + 35)) (by omega) stage11
      (fun next carried clock => header_carry_flag_excess_blobgas_word s next array count input inputLength scratch frame record word flag ceiling inputLimit env carried carried.2 clock)
  have stage13 : Reaches next (decodeHeaderAt 25) (fun post => HeaderCarryFlag s post array count input inputLength record word flag)
      ((headerRlpFieldCost inputLimit + 35) + 2 * (headerRlpFieldCost inputLimit + 35) +
        (headerRlpFieldCost inputLimit + 1) + 1 * (headerRlpFieldCost inputLimit + 35) +
        (headerRlpFieldCost inputLimit + 1) + 2 * (headerRlpFieldCost inputLimit + 1) +
        (headerRlpFieldCost inputLimit + 35) + 1 * (headerRlpFieldCost inputLimit + 1) +
        (headerRlpFieldCost inputLimit + 1) + 1 * (headerRlpFieldCost inputLimit + 35) +
        (headerRlpFieldCost inputLimit + 1) + 1 * (headerRlpFieldCost inputLimit + 35) +
        2 * (headerRlpFieldCost inputLimit + 1))      (decodeHeaderAt 56) :=
    reaches_trans_budget next (decodeHeaderAt 25) (decodeHeaderAt 52) (decodeHeaderAt 56) (fun post => HeaderCarryFlag s post array count input inputLength record word flag)
      (fun post => HeaderCarryFlag s post array count input inputLength record word flag)
      ((headerRlpFieldCost inputLimit + 35) + 2 * (headerRlpFieldCost inputLimit + 35) +
        (headerRlpFieldCost inputLimit + 1) + 1 * (headerRlpFieldCost inputLimit + 35) +
        (headerRlpFieldCost inputLimit + 1) + 2 * (headerRlpFieldCost inputLimit + 1) +
        (headerRlpFieldCost inputLimit + 35) + 1 * (headerRlpFieldCost inputLimit + 1) +
        (headerRlpFieldCost inputLimit + 1) + 1 * (headerRlpFieldCost inputLimit + 35) +
        (headerRlpFieldCost inputLimit + 1) + 1 * (headerRlpFieldCost inputLimit + 35)) (2 * (headerRlpFieldCost inputLimit + 1)) (by omega) stage12
      (fun next carried clock => header_carry_flag_last_bytes s next array count input inputLength scratch frame record word flag ceiling inputLimit env carried carried.2 clock)
  exact reaches_mono next _ _ _ _ _ _ (Nat.le_of_eq span.symm) (fun _ kept => kept) stage13


#print axioms decode_header_flag_span_from

/-- The whole actual early bytes chain from `decodeHeaderAt 11` to `decodeHeaderAt 23`
generates the state root word, keeps the slice table and the `arr`/`h` locals, and keeps
the `is_current` local of the entry state. -/
theorem decode_header_early_bytes_flag {F : Type} (s : PanSemStateFiniteExact 64 F)
    (array count input inputLength scratch frame record flag : BitVec 64) (ceiling inputLimit : Nat)
    (env : HeaderCarryEnv s array count input inputLength scratch frame record ceiling inputLimit)
    (atArray : s.locals.lookup (ofString "arr") = some (.val (.word array)))
    (atRecord : s.locals.lookup (ofString "h") = some (.val (.word record)))
    (table : RlpSliceInputPrefix s array input inputLength count.toNat)
    (atFlag : s.locals.lookup (ofString "is_current") = some (.val (.word flag)))
    (budget : 6 * headerDecoderUnitCost inputLimit ≤ s.clock) :
    Reaches s (decodeHeaderAt 11)
      (fun post => ∃ rooted : BitVec 64,
        HeaderSuffixCarry s post array count input inputLength record rooted ∧
        post.locals.lookup (ofString "is_current") = some (.val (.word flag)))
      (6 * headerDecoderUnitCost inputLimit) (decodeHeaderAt 23) := by
  have countBound := env.countBound
  have validSteps : ∀ item ∈ decodeHeaderEarlyBytes, item.1.toNat < count.toNat ∧ item.2.2 < 248 := by
    intro item member
    obtain ⟨index,width,offset⟩ := item
    have facts : index.toNat ≤ 6 ∧ offset < 248 := by
      simp only [decodeHeaderEarlyBytes,List.mem_cons,List.not_mem_nil,or_false] at member
      rcases member with ⟨rfl,rfl,rfl⟩ | ⟨rfl,rfl,rfl⟩ | ⟨rfl,rfl,rfl⟩ | ⟨rfl,rfl,rfl⟩ |
        ⟨rfl,rfl,rfl⟩ | ⟨rfl,rfl,rfl⟩ <;> decide
    obtain ⟨small,off⟩ := facts
    exact ⟨Nat.lt_of_le_of_lt small (by omega),off⟩
  have once : (decodeHeaderEarlyBytes.filter (fun item => item.2.2 == 32)).length = 1 := by decide
  have targetBound : 32 < 248 := by decide
  have costLe : 6 * (headerRlpFieldCost inputLimit + 1) ≤ 6 * headerDecoderUnitCost inputLimit := by
    unfold headerDecoderUnitCost
    exact Nat.mul_le_mul_left 6 (by omega)
  have chainBudget : 6 * (headerRlpFieldCost inputLimit + 1) ≤ s.clock :=
    Nat.le_trans costLe budget
  have chain := header_bytes_chain_written_content s array count input inputLength scratch frame record ceiling
    inputLimit decodeHeaderEarlyBytes (decodeHeaderAt 23) 32 validSteps once targetBound atArray atRecord env.before
    env.recordFits table env.above env.fits env.inputBound env.limitBound env.scratchGlobal env.frameGlobal env.code
    env.orderedFrame env.framePositive env.scratchBelow env.arena chainBudget
  rw [source_decode_header_early_bytes]
  refine reaches_mono s _ (decodeHeaderAt 23) _ _ _ _ costLe ?_ chain
  intro post kept
  obtain ⟨rooted,readable,_,tablePost,localsPost,domainPost,codePost,globalsPost,_⟩ := kept
  have atArrayPost : post.locals.lookup (ofString "arr") = some (.val (.word array)) :=
    (localsPost (ofString "arr") (by decide)).trans atArray
  have atRecordPost : post.locals.lookup (ofString "h") = some (.val (.word record)) :=
    (localsPost (ofString "h") (by decide)).trans atRecord
  have atFlagPost : post.locals.lookup (ofString "is_current") = some (.val (.word flag)) :=
    (localsPost (ofString "is_current") (by decide)).trans atFlag
  exact ⟨rooted,⟨readable,domainPost,codePost,globalsPost,tablePost,atArrayPost,atRecordPost⟩,atFlagPost⟩

#print axioms decode_header_early_bytes_flag

/-- The whole actual header body from `decodeHeaderAt 11` to `decodeHeaderAt 56` keeps
the carry together with the `is_current` local of the entry state. -/
theorem decode_header_whole_flag {F : Type} (s : PanSemStateFiniteExact 64 F)
    (array count input inputLength scratch frame record flag : BitVec 64) (ceiling inputLimit : Nat)
    (env : HeaderCarryEnv s array count input inputLength scratch frame record ceiling inputLimit)
    (atArray : s.locals.lookup (ofString "arr") = some (.val (.word array)))
    (atRecord : s.locals.lookup (ofString "h") = some (.val (.word record)))
    (table : RlpSliceInputPrefix s array input inputLength count.toNat)
    (atFlag : s.locals.lookup (ofString "is_current") = some (.val (.word flag)))
    (budget : headerWholeFieldCost inputLimit ≤ s.clock) :
    Reaches s (decodeHeaderAt 11)
      (fun post => ∃ rooted : BitVec 64, HeaderCarryFlag s post array count input inputLength record rooted flag)
      (headerWholeFieldCost inputLimit) (decodeHeaderAt 56) := by
  unfold headerWholeFieldCost at budget
  have countBound := env.countBound
  have early := decode_header_early_bytes_flag s array count input inputLength scratch frame record flag ceiling inputLimit
    env atArray atRecord table atFlag (by omega)
  apply reaches_trans_budget s (decodeHeaderAt 11) (decodeHeaderAt 23) (decodeHeaderAt 56) _
    _ (6 * headerDecoderUnitCost inputLimit)
    ((headerRlpFieldCost inputLimit + 35) + headerDecoderSpanCost inputLimit) (by omega) early
  intro mid facts remaining
  obtain ⟨earlyWord,carried,atFlagMid⟩ := facts
  obtain ⟨rootMem,domain,code,globals,tableMid,atArrayMid,atRecordMid⟩ := carried
  have scratchMid : mid.globals.lookup (ofString "scratch_ptr") = some (.val (.word scratch)) :=
    (globals (ofString "scratch_ptr")).trans env.scratchGlobal
  have frameMid : mid.globals.lookup (ofString "frame_mem_ptr") = some (.val (.word frame)) :=
    (globals (ofString "frame_mem_ptr")).trans env.frameGlobal
  have arenaMid : ∀ address : BitVec 64, frame.toNat ≤ address.toNat → address.toNat < ceiling →
      mid.memaddrs address := by
    intro address lo hi
    rw [domain]
    exact env.arena address lo hi
  have difficulty := decode_header_difficulty_content_frame mid array count input inputLength scratch frame record
    ceiling inputLimit atArrayMid atRecordMid env.before env.recordFits tableMid (by omega) env.above env.fits
    env.inputBound env.limitBound scratchMid frameMid (code.trans env.code) env.orderedFrame env.framePositive
    env.scratchBelow arenaMid (by omega)
  apply reaches_trans_budget mid (decodeHeaderAt 23) (decodeHeaderAt 25) (decodeHeaderAt 56) _
    _ (headerRlpFieldCost inputLimit + 35) (headerDecoderSpanCost inputLimit) (by omega) difficulty
  intro late facts2 remaining2
  obtain ⟨first,second,third,fourth,localsLate,tableLate,domainLate,codeLate,globalsLate,memoryLate⟩ := facts2
  have rootAbove : ceiling ≤ (record + 32#64).toNat :=
    record_offset_above_ceiling array count record ceiling 32 env.above env.before (by decide) env.recordFits
  have rootLate : late.memory (record + 32#64) = .word earlyWord :=
    (memoryLate (record + 32#64) rootAbove
      (record_root_apart_offset record (BitVec.ofNat 64 64) env.recordFits (by decide) (by decide))
      (by rw [BitVec.add_assoc]
          exact record_root_apart_offset record ((BitVec.ofNat 64 64) + 8#64) env.recordFits (by decide) (by decide))
      (by rw [BitVec.add_assoc]
          exact record_root_apart_offset record ((BitVec.ofNat 64 64) + 16#64) env.recordFits (by decide) (by decide))
      (by rw [BitVec.add_assoc]
          exact record_root_apart_offset record ((BitVec.ofNat 64 64) + 24#64) env.recordFits (by decide)
            (by decide))).trans rootMem
  have atArrayLate : late.locals.lookup (ofString "arr") = some (.val (.word array)) := by
    rw [localsLate]
    simpa (config := {decide := true}) [HolFiniteMapExact.lookup_update,FUPDATE] using atArrayMid
  have atRecordLate : late.locals.lookup (ofString "h") = some (.val (.word record)) := by
    rw [localsLate]
    simpa (config := {decide := true}) [HolFiniteMapExact.lookup_update,FUPDATE] using atRecordMid
  have atFlagLate : late.locals.lookup (ofString "is_current") = some (.val (.word flag)) := by
    rw [localsLate]
    simpa (config := {decide := true}) [HolFiniteMapExact.lookup_update,FUPDATE] using atFlagMid
  have entryFlag : HeaderCarryFlag s late array count input inputLength record earlyWord flag :=
    ⟨⟨rootLate,domainLate.trans domain,codeLate.trans code,
        fun global => (globalsLate global).trans (globals global),tableLate,atArrayLate,atRecordLate⟩,atFlagLate⟩
  refine reaches_mono late (decodeHeaderAt 25) (decodeHeaderAt 56) _ _ _ _ (le_refl _) ?_
    (decode_header_flag_span_from s late array count input inputLength scratch frame record earlyWord ceiling
      inputLimit env flag entryFlag (by omega))
  intro post kept
  exact ⟨earlyWord,kept⟩

#print axioms decode_header_whole_flag

/-- The whole actual header body from `decodeHeaderAt 11` to the actual return at
`decodeHeaderAt 57` keeps the carry together with the `is_current` local. -/
theorem decode_header_whole_body_flag {F : Type} (s : PanSemStateFiniteExact 64 F)
    (array count input inputLength scratch frame record flag : BitVec 64) (ceiling inputLimit : Nat)
    (env : HeaderCarryEnv s array count input inputLength scratch frame record ceiling inputLimit)
    (atArray : s.locals.lookup (ofString "arr") = some (.val (.word array)))
    (atRecord : s.locals.lookup (ofString "h") = some (.val (.word record)))
    (table : RlpSliceInputPrefix s array input inputLength count.toNat)
    (atFlag : s.locals.lookup (ofString "is_current") = some (.val (.word flag)))
    (currentBound : flag ≠ 0 → 23 ≤ count.toNat)
    (budget : headerWholeBodyCost inputLimit ≤ s.clock) :
    Reaches s (decodeHeaderAt 11)
      (fun post => ∃ rooted : BitVec 64, HeaderSuffixCarry s post array count input inputLength record rooted)
      (headerWholeBodyCost inputLimit) (decodeHeaderAt 57) := by
  unfold headerWholeBodyCost at budget
  apply reaches_trans_budget s (decodeHeaderAt 11) (decodeHeaderAt 56) (decodeHeaderAt 57) _ _
    (headerWholeFieldCost inputLimit)
    ((headerRlpFieldCost inputLimit + 1) +
      ((headerRlpFieldCost inputLimit + 1) + (headerRlpFieldCost inputLimit + 35))) (by omega)
    (decode_header_whole_flag s array count input inputLength scratch frame record flag ceiling inputLimit env
      atArray atRecord table atFlag (by omega))
  intro next carried remaining
  obtain ⟨rooted,carry,atFlagNext⟩ := carried
  refine reaches_mono next (decodeHeaderAt 56) (decodeHeaderAt 57) _ _ _ _ (le_refl _) ?_
    (header_carry_suffix s next array count input inputLength scratch frame record rooted ceiling inputLimit env carry
      flag atFlagNext currentBound (by omega))
  intro post final
  exact ⟨rooted,final⟩

#print axioms decode_header_whole_body_flag

/-- A returned execution of the whole actual header body, for either header kind, returns
its allocated record as the header pointer and leaves the generated state root word
readable at `pointer + 32`, together with the record domain, the code, the globals and the
record geometry. -/
theorem decode_header_whole_returned_root_flag {F : Type} (s post : PanSemStateFiniteExact 64 F)
    (array count input inputLength scratch frame record flag : BitVec 64) (ceiling inputLimit : Nat)
    (env : HeaderCarryEnv s array count input inputLength scratch frame record ceiling inputLimit)
    (atArray : s.locals.lookup (ofString "arr") = some (.val (.word array)))
    (atRecord : s.locals.lookup (ofString "h") = some (.val (.word record)))
    (table : RlpSliceInputPrefix s array input inputLength count.toNat)
    (atFlag : s.locals.lookup (ofString "is_current") = some (.val (.word flag)))
    (currentBound : flag ≠ 0 → 23 ≤ count.toNat)
    (budget : headerWholeBodyCost inputLimit ≤ s.clock) (value : ValueHOL 64)
    (run : evaluateHOLFiniteState s (decodeHeaderAt 11) = (some (.returned value),post)) :
    value = .val (.word record) ∧
      (∃ rooted : BitVec 64, post.memory (record + 32#64) = .word rooted) ∧
      post.memaddrs = s.memaddrs ∧ post.code = s.code ∧
      (∀ global : MlS, post.globals.lookup global = s.globals.lookup global) ∧
      array.toNat + count.toNat * 16 ≤ record.toNat ∧ record.toNat + 248 < 2^64 := by
  have reached := decode_header_whole_body_flag s array count input inputLength scratch frame record flag ceiling
    inputLimit env atArray atRecord table atFlag currentBound budget
  obtain ⟨ready,carried,_,_,agreement,returnedTail⟩ := reaches_returned_continuation s (decodeHeaderAt 11)
    (decodeHeaderAt 57) _ (headerWholeBodyCost inputLimit) value reached (by rw [run])
  have tailMemory : (evaluateHOLFiniteState ready (decodeHeaderAt 57)).2.memory = ready.memory := by
    rw [source_decode_header_return,evaluateHOLFiniteState_return]
    repeat first | split | rfl
  have tailGlobals : (evaluateHOLFiniteState ready (decodeHeaderAt 57)).2.globals = ready.globals := by
    rw [source_decode_header_return,evaluateHOLFiniteState_return]
    repeat first | split | rfl
  have sourceMemory := agreement.2.2.1
  have sourceGlobals := agreement.2.2.2.1
  rw [run] at sourceMemory sourceGlobals
  have metadata := evaluateHOLFiniteState_metadata s (decodeHeaderAt 11)
  rw [run] at metadata
  obtain ⟨rooted,rootMem,domain,code,globals,_,atRecordReady⟩ := carried
  refine ⟨?_,⟨rooted,?_⟩,metadata.2.1,metadata.1,?_,env.before,env.recordFits⟩
  · rw [source_decode_header_return,evaluateHOLFiniteState_return] at returnedTail
    simpa [evalHOLExact,atRecordReady,shapeOfHOLExact] using returnedTail.symm
  · rw [sourceMemory,tailMemory]
    exact rootMem
  · intro global
    rw [sourceGlobals,tailGlobals]
    exact globals global

#print axioms decode_header_whole_returned_root_flag
end InitECandidate.Runtime
