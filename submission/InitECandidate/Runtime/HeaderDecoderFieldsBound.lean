import InitECandidate.Runtime.HeaderDecoderExtraContextReach
import InitECandidate.Runtime.RunBoundedReaches
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
set_option maxRecDepth 100000
set_option maxHeartbeats 200000

theorem header_decoder_at56_bounded {F : Type} (s : PanSemStateFiniteExact 64 F)
    (array count input inputLength scratch frame record flag : BitVec 64) (ceiling inputLimit : Nat)
    (g : HeaderDecoderGeometry array count inputLength scratch frame record flag ceiling inputLimit)
    (c : HeaderDecoderContext s array count input inputLength scratch frame record flag ceiling)
    (budget : 3 * headerDecoderUnitCost inputLimit ≤ s.clock) :
    RunBounded s (decodeHeaderAt 56) (3 * headerDecoderUnitCost inputLimit) := by
  exact decode_header_final_suffix_bounded s array count input inputLength scratch frame record ceiling inputLimit flag c.atFlag
    g.currentCount c.atArray c.atRecord g.before g.recordFits c.table g.above g.fits g.inputBound g.limitBound c.scratchGlobal c.frameGlobal
    c.code g.orderedFrame g.framePositive g.scratchBelow c.arena budget

#print axioms header_decoder_at56_bounded

theorem header_decoder_at52_bounded {F : Type} (s : PanSemStateFiniteExact 64 F)
    (array count input inputLength scratch frame record flag : BitVec 64) (ceiling inputLimit : Nat)
    (g : HeaderDecoderGeometry array count inputLength scratch frame record flag ceiling inputLimit)
    (c : HeaderDecoderContext s array count input inputLength scratch frame record flag ceiling)
    (budget : 5 * headerDecoderUnitCost inputLimit ≤ s.clock) :
    RunBounded s (decodeHeaderAt 52) (5 * headerDecoderUnitCost inputLimit) := by
  have split : 5 * headerDecoderUnitCost inputLimit =
      2 * headerDecoderUnitCost inputLimit + 3 * headerDecoderUnitCost inputLimit := by omega
  rw [split] at budget ⊢
  apply RunBounded.ofReaches budget
    (header_context_last_bytes_reaches s array count input inputLength scratch frame record flag ceiling inputLimit g c (by omega))
  intro next ready remaining
  exact header_decoder_at56_bounded next array count input inputLength scratch frame record flag ceiling inputLimit g ready remaining

#print axioms header_decoder_at52_bounded

theorem header_decoder_at50_bounded {F : Type} (s : PanSemStateFiniteExact 64 F)
    (array count input inputLength scratch frame record flag : BitVec 64) (ceiling inputLimit : Nat)
    (g : HeaderDecoderGeometry array count inputLength scratch frame record flag ceiling inputLimit)
    (c : HeaderDecoderContext s array count input inputLength scratch frame record flag ceiling)
    (budget : 6 * headerDecoderUnitCost inputLimit ≤ s.clock) :
    RunBounded s (decodeHeaderAt 50) (6 * headerDecoderUnitCost inputLimit) := by
  have split : 6 * headerDecoderUnitCost inputLimit =
      1 * headerDecoderUnitCost inputLimit + 5 * headerDecoderUnitCost inputLimit := by omega
  rw [split] at budget ⊢
  apply RunBounded.ofReaches budget
    (header_context_excess_blobgas_word_reaches s array count input inputLength scratch frame record flag ceiling inputLimit g c (by omega))
  intro next ready remaining
  exact header_decoder_at52_bounded next array count input inputLength scratch frame record flag ceiling inputLimit g ready remaining

#print axioms header_decoder_at50_bounded

theorem header_decoder_at49_bounded {F : Type} (s : PanSemStateFiniteExact 64 F)
    (array count input inputLength scratch frame record flag : BitVec 64) (ceiling inputLimit : Nat)
    (g : HeaderDecoderGeometry array count inputLength scratch frame record flag ceiling inputLimit)
    (c : HeaderDecoderContext s array count input inputLength scratch frame record flag ceiling)
    (budget : 7 * headerDecoderUnitCost inputLimit ≤ s.clock) :
    RunBounded s (decodeHeaderAt 49) (7 * headerDecoderUnitCost inputLimit) := by
  have split : 7 * headerDecoderUnitCost inputLimit =
      1 * headerDecoderUnitCost inputLimit + 6 * headerDecoderUnitCost inputLimit := by omega
  rw [split] at budget ⊢
  apply RunBounded.ofReaches budget
    (header_context_excess_blobgas_reaches s array count input inputLength scratch frame record flag ceiling inputLimit g c (by omega))
  intro next ready remaining
  exact header_decoder_at50_bounded next array count input inputLength scratch frame record flag ceiling inputLimit g ready remaining

#print axioms header_decoder_at49_bounded

theorem header_decoder_at47_bounded {F : Type} (s : PanSemStateFiniteExact 64 F)
    (array count input inputLength scratch frame record flag : BitVec 64) (ceiling inputLimit : Nat)
    (g : HeaderDecoderGeometry array count inputLength scratch frame record flag ceiling inputLimit)
    (c : HeaderDecoderContext s array count input inputLength scratch frame record flag ceiling)
    (budget : 8 * headerDecoderUnitCost inputLimit ≤ s.clock) :
    RunBounded s (decodeHeaderAt 47) (8 * headerDecoderUnitCost inputLimit) := by
  have split : 8 * headerDecoderUnitCost inputLimit =
      1 * headerDecoderUnitCost inputLimit + 7 * headerDecoderUnitCost inputLimit := by omega
  rw [split] at budget ⊢
  apply RunBounded.ofReaches budget
    (header_context_blobgas_word_reaches s array count input inputLength scratch frame record flag ceiling inputLimit g c (by omega))
  intro next ready remaining
  exact header_decoder_at49_bounded next array count input inputLength scratch frame record flag ceiling inputLimit g ready remaining

#print axioms header_decoder_at47_bounded

theorem header_decoder_at46_bounded {F : Type} (s : PanSemStateFiniteExact 64 F)
    (array count input inputLength scratch frame record flag : BitVec 64) (ceiling inputLimit : Nat)
    (g : HeaderDecoderGeometry array count inputLength scratch frame record flag ceiling inputLimit)
    (c : HeaderDecoderContext s array count input inputLength scratch frame record flag ceiling)
    (budget : 9 * headerDecoderUnitCost inputLimit ≤ s.clock) :
    RunBounded s (decodeHeaderAt 46) (9 * headerDecoderUnitCost inputLimit) := by
  have split : 9 * headerDecoderUnitCost inputLimit =
      1 * headerDecoderUnitCost inputLimit + 8 * headerDecoderUnitCost inputLimit := by omega
  rw [split] at budget ⊢
  apply RunBounded.ofReaches budget
    (header_context_blobgas_reaches s array count input inputLength scratch frame record flag ceiling inputLimit g c (by omega))
  intro next ready remaining
  exact header_decoder_at47_bounded next array count input inputLength scratch frame record flag ceiling inputLimit g ready remaining

#print axioms header_decoder_at46_bounded

theorem header_decoder_at44_bounded {F : Type} (s : PanSemStateFiniteExact 64 F)
    (array count input inputLength scratch frame record flag : BitVec 64) (ceiling inputLimit : Nat)
    (g : HeaderDecoderGeometry array count inputLength scratch frame record flag ceiling inputLimit)
    (c : HeaderDecoderContext s array count input inputLength scratch frame record flag ceiling)
    (budget : 10 * headerDecoderUnitCost inputLimit ≤ s.clock) :
    RunBounded s (decodeHeaderAt 44) (10 * headerDecoderUnitCost inputLimit) := by
  have split : 10 * headerDecoderUnitCost inputLimit =
      1 * headerDecoderUnitCost inputLimit + 9 * headerDecoderUnitCost inputLimit := by omega
  rw [split] at budget ⊢
  apply RunBounded.ofReaches budget
    (header_context_withdrawals_reaches s array count input inputLength scratch frame record flag ceiling inputLimit g c (by omega))
  intro next ready remaining
  exact header_decoder_at46_bounded next array count input inputLength scratch frame record flag ceiling inputLimit g ready remaining

#print axioms header_decoder_at44_bounded

theorem header_decoder_at42_bounded {F : Type} (s : PanSemStateFiniteExact 64 F)
    (array count input inputLength scratch frame record flag : BitVec 64) (ceiling inputLimit : Nat)
    (g : HeaderDecoderGeometry array count inputLength scratch frame record flag ceiling inputLimit)
    (c : HeaderDecoderContext s array count input inputLength scratch frame record flag ceiling)
    (budget : 11 * headerDecoderUnitCost inputLimit ≤ s.clock) :
    RunBounded s (decodeHeaderAt 42) (11 * headerDecoderUnitCost inputLimit) := by
  have split : 11 * headerDecoderUnitCost inputLimit =
      1 * headerDecoderUnitCost inputLimit + 10 * headerDecoderUnitCost inputLimit := by omega
  rw [split] at budget ⊢
  apply RunBounded.ofReaches budget
    (header_context_basefee_reaches s array count input inputLength scratch frame record flag ceiling inputLimit g c (by omega))
  intro next ready remaining
  exact header_decoder_at44_bounded next array count input inputLength scratch frame record flag ceiling inputLimit g ready remaining

#print axioms header_decoder_at42_bounded

theorem header_decoder_at38_bounded {F : Type} (s : PanSemStateFiniteExact 64 F)
    (array count input inputLength scratch frame record flag : BitVec 64) (ceiling inputLimit : Nat)
    (g : HeaderDecoderGeometry array count inputLength scratch frame record flag ceiling inputLimit)
    (c : HeaderDecoderContext s array count input inputLength scratch frame record flag ceiling)
    (budget : 13 * headerDecoderUnitCost inputLimit ≤ s.clock) :
    RunBounded s (decodeHeaderAt 38) (13 * headerDecoderUnitCost inputLimit) := by
  have split : 13 * headerDecoderUnitCost inputLimit =
      2 * headerDecoderUnitCost inputLimit + 11 * headerDecoderUnitCost inputLimit := by omega
  rw [split] at budget ⊢
  apply RunBounded.ofReaches budget
    (header_context_middle_bytes_reaches s array count input inputLength scratch frame record flag ceiling inputLimit g c (by omega))
  intro next ready remaining
  exact header_decoder_at42_bounded next array count input inputLength scratch frame record flag ceiling inputLimit g ready remaining

#print axioms header_decoder_at38_bounded

theorem header_decoder_at35_bounded {F : Type} (s : PanSemStateFiniteExact 64 F)
    (array count input inputLength scratch frame record flag : BitVec 64) (ceiling inputLimit : Nat)
    (g : HeaderDecoderGeometry array count inputLength scratch frame record flag ceiling inputLimit)
    (c : HeaderDecoderContext s array count input inputLength scratch frame record flag ceiling)
    (budget : 14 * headerDecoderUnitCost inputLimit ≤ s.clock) :
    RunBounded s (decodeHeaderAt 35) (14 * headerDecoderUnitCost inputLimit) := by
  have split : 14 * headerDecoderUnitCost inputLimit =
      1 * headerDecoderUnitCost inputLimit + 13 * headerDecoderUnitCost inputLimit := by omega
  rw [split] at budget ⊢
  apply RunBounded.ofReaches budget
    (header_context_extra_reaches s array count input inputLength scratch frame record flag ceiling inputLimit g c (by omega))
  intro next ready remaining
  exact header_decoder_at38_bounded next array count input inputLength scratch frame record flag ceiling inputLimit g ready remaining

#print axioms header_decoder_at35_bounded

theorem header_decoder_at33_bounded {F : Type} (s : PanSemStateFiniteExact 64 F)
    (array count input inputLength scratch frame record flag : BitVec 64) (ceiling inputLimit : Nat)
    (g : HeaderDecoderGeometry array count inputLength scratch frame record flag ceiling inputLimit)
    (c : HeaderDecoderContext s array count input inputLength scratch frame record flag ceiling)
    (budget : 15 * headerDecoderUnitCost inputLimit ≤ s.clock) :
    RunBounded s (decodeHeaderAt 33) (15 * headerDecoderUnitCost inputLimit) := by
  have split : 15 * headerDecoderUnitCost inputLimit =
      1 * headerDecoderUnitCost inputLimit + 14 * headerDecoderUnitCost inputLimit := by omega
  rw [split] at budget ⊢
  apply RunBounded.ofReaches budget
    (header_context_timestamp_word_reaches s array count input inputLength scratch frame record flag ceiling inputLimit g c (by omega))
  intro next ready remaining
  exact header_decoder_at35_bounded next array count input inputLength scratch frame record flag ceiling inputLimit g ready remaining

#print axioms header_decoder_at33_bounded

theorem header_decoder_at31_bounded {F : Type} (s : PanSemStateFiniteExact 64 F)
    (array count input inputLength scratch frame record flag : BitVec 64) (ceiling inputLimit : Nat)
    (g : HeaderDecoderGeometry array count inputLength scratch frame record flag ceiling inputLimit)
    (c : HeaderDecoderContext s array count input inputLength scratch frame record flag ceiling)
    (budget : 16 * headerDecoderUnitCost inputLimit ≤ s.clock) :
    RunBounded s (decodeHeaderAt 31) (16 * headerDecoderUnitCost inputLimit) := by
  have split : 16 * headerDecoderUnitCost inputLimit =
      1 * headerDecoderUnitCost inputLimit + 15 * headerDecoderUnitCost inputLimit := by omega
  rw [split] at budget ⊢
  apply RunBounded.ofReaches budget
    (header_context_timestamp_reaches s array count input inputLength scratch frame record flag ceiling inputLimit g c (by omega))
  intro next ready remaining
  exact header_decoder_at33_bounded next array count input inputLength scratch frame record flag ceiling inputLimit g ready remaining

#print axioms header_decoder_at31_bounded

theorem header_decoder_at27_bounded {F : Type} (s : PanSemStateFiniteExact 64 F)
    (array count input inputLength scratch frame record flag : BitVec 64) (ceiling inputLimit : Nat)
    (g : HeaderDecoderGeometry array count inputLength scratch frame record flag ceiling inputLimit)
    (c : HeaderDecoderContext s array count input inputLength scratch frame record flag ceiling)
    (budget : 18 * headerDecoderUnitCost inputLimit ≤ s.clock) :
    RunBounded s (decodeHeaderAt 27) (18 * headerDecoderUnitCost inputLimit) := by
  have split : 18 * headerDecoderUnitCost inputLimit =
      2 * headerDecoderUnitCost inputLimit + 16 * headerDecoderUnitCost inputLimit := by omega
  rw [split] at budget ⊢
  apply RunBounded.ofReaches budget
    (header_context_words_reaches s array count input inputLength scratch frame record flag ceiling inputLimit g c (by omega))
  intro next ready remaining
  exact header_decoder_at31_bounded next array count input inputLength scratch frame record flag ceiling inputLimit g ready remaining

#print axioms header_decoder_at27_bounded

theorem header_decoder_at25_bounded {F : Type} (s : PanSemStateFiniteExact 64 F)
    (array count input inputLength scratch frame record flag : BitVec 64) (ceiling inputLimit : Nat)
    (g : HeaderDecoderGeometry array count inputLength scratch frame record flag ceiling inputLimit)
    (c : HeaderDecoderContext s array count input inputLength scratch frame record flag ceiling)
    (budget : 19 * headerDecoderUnitCost inputLimit ≤ s.clock) :
    RunBounded s (decodeHeaderAt 25) (19 * headerDecoderUnitCost inputLimit) := by
  have split : 19 * headerDecoderUnitCost inputLimit =
      1 * headerDecoderUnitCost inputLimit + 18 * headerDecoderUnitCost inputLimit := by omega
  rw [split] at budget ⊢
  apply RunBounded.ofReaches budget
    (header_context_word_reaches s array count input inputLength scratch frame record flag ceiling inputLimit g c (by omega))
  intro next ready remaining
  exact header_decoder_at27_bounded next array count input inputLength scratch frame record flag ceiling inputLimit g ready remaining

#print axioms header_decoder_at25_bounded

theorem header_decoder_at23_bounded {F : Type} (s : PanSemStateFiniteExact 64 F)
    (array count input inputLength scratch frame record flag : BitVec 64) (ceiling inputLimit : Nat)
    (g : HeaderDecoderGeometry array count inputLength scratch frame record flag ceiling inputLimit)
    (c : HeaderDecoderContext s array count input inputLength scratch frame record flag ceiling)
    (budget : 20 * headerDecoderUnitCost inputLimit ≤ s.clock) :
    RunBounded s (decodeHeaderAt 23) (20 * headerDecoderUnitCost inputLimit) := by
  have split : 20 * headerDecoderUnitCost inputLimit =
      1 * headerDecoderUnitCost inputLimit + 19 * headerDecoderUnitCost inputLimit := by omega
  rw [split] at budget ⊢
  apply RunBounded.ofReaches budget
    (header_context_difficulty_reaches s array count input inputLength scratch frame record flag ceiling inputLimit g c (by omega))
  intro next ready remaining
  exact header_decoder_at25_bounded next array count input inputLength scratch frame record flag ceiling inputLimit g ready remaining

#print axioms header_decoder_at23_bounded

theorem header_decoder_at11_bounded {F : Type} (s : PanSemStateFiniteExact 64 F)
    (array count input inputLength scratch frame record flag : BitVec 64) (ceiling inputLimit : Nat)
    (g : HeaderDecoderGeometry array count inputLength scratch frame record flag ceiling inputLimit)
    (c : HeaderDecoderContext s array count input inputLength scratch frame record flag ceiling)
    (budget : 26 * headerDecoderUnitCost inputLimit ≤ s.clock) :
    RunBounded s (decodeHeaderAt 11) (26 * headerDecoderUnitCost inputLimit) := by
  have split : 26 * headerDecoderUnitCost inputLimit =
      6 * headerDecoderUnitCost inputLimit + 20 * headerDecoderUnitCost inputLimit := by omega
  rw [split] at budget ⊢
  apply RunBounded.ofReaches budget
    (header_context_bytes_reaches s array count input inputLength scratch frame record flag ceiling inputLimit g c (by omega))
  intro next ready remaining
  exact header_decoder_at23_bounded next array count input inputLength scratch frame record flag ceiling inputLimit g ready remaining

#print axioms header_decoder_at11_bounded

theorem header_decoder_at9_bounded {F : Type} (s : PanSemStateFiniteExact 64 F)
    (array count input inputLength scratch frame record flag : BitVec 64) (ceiling inputLimit : Nat)
    (g : HeaderDecoderGeometry array count inputLength scratch frame record flag ceiling inputLimit)
    (c : HeaderDecoderContext s array count input inputLength scratch frame record flag ceiling)
    (budget : 27 * headerDecoderUnitCost inputLimit ≤ s.clock) :
    RunBounded s (decodeHeaderAt 9) (27 * headerDecoderUnitCost inputLimit) := by
  have split : 27 * headerDecoderUnitCost inputLimit =
      1 * headerDecoderUnitCost inputLimit + 26 * headerDecoderUnitCost inputLimit := by omega
  rw [split] at budget ⊢
  apply RunBounded.ofReaches budget
    (header_context_first_reaches s array count input inputLength scratch frame record flag ceiling inputLimit g c (by omega))
  intro next ready remaining
  exact header_decoder_at11_bounded next array count input inputLength scratch frame record flag ceiling inputLimit g ready remaining

#print axioms header_decoder_at9_bounded

end InitECandidate.Runtime
