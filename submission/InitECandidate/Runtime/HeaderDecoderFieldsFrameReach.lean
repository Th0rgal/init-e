import InitECandidate.Runtime.HeaderDecoderExtraFrameReach
import InitECandidate.Runtime.RunBoundedReaches
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
set_option maxRecDepth 100000
set_option maxHeartbeats 200000

theorem HeaderDecoderFrame.trans {F : Type} {s middle post : PanSemStateFiniteExact 64 F}
    {array count input inputLength scratch frame record flag : BitVec 64} {ceiling : Nat}
    (first : HeaderDecoderFrame s middle array count input inputLength scratch frame record flag ceiling)
    (second : HeaderDecoderFrame middle post array count input inputLength scratch frame record flag ceiling) :
    HeaderDecoderFrame s post array count input inputLength scratch frame record flag ceiling :=
  ⟨second.context,second.domain.trans first.domain,second.code.trans first.code,
    fun name => (second.globals name).trans (first.globals name),
    fun address lo hi => (second.memory address lo hi).trans (first.memory address lo hi)⟩

theorem header_fields_at52_frame_reaches {F : Type} (s : PanSemStateFiniteExact 64 F)
    (array count input inputLength scratch frame record flag : BitVec 64) (ceiling inputLimit : Nat)
    (g : HeaderDecoderGeometry array count inputLength scratch frame record flag ceiling inputLimit)
    (c : HeaderDecoderContext s array count input inputLength scratch frame record flag ceiling)
    (budget : 2 * headerDecoderUnitCost inputLimit ≤ s.clock) :
    Reaches s (decodeHeaderAt 52)
      (fun post => HeaderDecoderFrame s post array count input inputLength scratch frame record flag ceiling)
      (2 * headerDecoderUnitCost inputLimit) (decodeHeaderAt 56) :=
  header_frame_last_bytes_reaches s array count input inputLength scratch frame record flag ceiling inputLimit g c budget

#print axioms header_fields_at52_frame_reaches

theorem header_fields_at50_frame_reaches {F : Type} (s : PanSemStateFiniteExact 64 F)
    (array count input inputLength scratch frame record flag : BitVec 64) (ceiling inputLimit : Nat)
    (g : HeaderDecoderGeometry array count inputLength scratch frame record flag ceiling inputLimit)
    (c : HeaderDecoderContext s array count input inputLength scratch frame record flag ceiling)
    (budget : 3 * headerDecoderUnitCost inputLimit ≤ s.clock) :
    Reaches s (decodeHeaderAt 50)
      (fun post => HeaderDecoderFrame s post array count input inputLength scratch frame record flag ceiling)
      (3 * headerDecoderUnitCost inputLimit) (decodeHeaderAt 56) := by
  have split : 3 * headerDecoderUnitCost inputLimit =
      1 * headerDecoderUnitCost inputLimit + 2 * headerDecoderUnitCost inputLimit := by omega
  rw [split] at budget ⊢
  apply reaches_trans_budget s (decodeHeaderAt 50) (decodeHeaderAt 52) (decodeHeaderAt 56) _ _
    (1 * headerDecoderUnitCost inputLimit) (2 * headerDecoderUnitCost inputLimit) budget
    (header_frame_excess_blobgas_word_reaches s array count input inputLength scratch frame record flag ceiling inputLimit g c (by omega))
  intro next kept remaining
  apply reaches_mono next (decodeHeaderAt 52) (decodeHeaderAt 56) _ _ _ _ (le_refl _) ?_
    (header_fields_at52_frame_reaches next array count input inputLength scratch frame record flag ceiling inputLimit g kept.context remaining)
  intro post framed
  exact kept.trans framed

#print axioms header_fields_at50_frame_reaches

theorem header_fields_at49_frame_reaches {F : Type} (s : PanSemStateFiniteExact 64 F)
    (array count input inputLength scratch frame record flag : BitVec 64) (ceiling inputLimit : Nat)
    (g : HeaderDecoderGeometry array count inputLength scratch frame record flag ceiling inputLimit)
    (c : HeaderDecoderContext s array count input inputLength scratch frame record flag ceiling)
    (budget : 4 * headerDecoderUnitCost inputLimit ≤ s.clock) :
    Reaches s (decodeHeaderAt 49)
      (fun post => HeaderDecoderFrame s post array count input inputLength scratch frame record flag ceiling)
      (4 * headerDecoderUnitCost inputLimit) (decodeHeaderAt 56) := by
  have split : 4 * headerDecoderUnitCost inputLimit =
      1 * headerDecoderUnitCost inputLimit + 3 * headerDecoderUnitCost inputLimit := by omega
  rw [split] at budget ⊢
  apply reaches_trans_budget s (decodeHeaderAt 49) (decodeHeaderAt 50) (decodeHeaderAt 56) _ _
    (1 * headerDecoderUnitCost inputLimit) (3 * headerDecoderUnitCost inputLimit) budget
    (header_frame_excess_blobgas_reaches s array count input inputLength scratch frame record flag ceiling inputLimit g c (by omega))
  intro next kept remaining
  apply reaches_mono next (decodeHeaderAt 50) (decodeHeaderAt 56) _ _ _ _ (le_refl _) ?_
    (header_fields_at50_frame_reaches next array count input inputLength scratch frame record flag ceiling inputLimit g kept.context remaining)
  intro post framed
  exact kept.trans framed

#print axioms header_fields_at49_frame_reaches

theorem header_fields_at47_frame_reaches {F : Type} (s : PanSemStateFiniteExact 64 F)
    (array count input inputLength scratch frame record flag : BitVec 64) (ceiling inputLimit : Nat)
    (g : HeaderDecoderGeometry array count inputLength scratch frame record flag ceiling inputLimit)
    (c : HeaderDecoderContext s array count input inputLength scratch frame record flag ceiling)
    (budget : 5 * headerDecoderUnitCost inputLimit ≤ s.clock) :
    Reaches s (decodeHeaderAt 47)
      (fun post => HeaderDecoderFrame s post array count input inputLength scratch frame record flag ceiling)
      (5 * headerDecoderUnitCost inputLimit) (decodeHeaderAt 56) := by
  have split : 5 * headerDecoderUnitCost inputLimit =
      1 * headerDecoderUnitCost inputLimit + 4 * headerDecoderUnitCost inputLimit := by omega
  rw [split] at budget ⊢
  apply reaches_trans_budget s (decodeHeaderAt 47) (decodeHeaderAt 49) (decodeHeaderAt 56) _ _
    (1 * headerDecoderUnitCost inputLimit) (4 * headerDecoderUnitCost inputLimit) budget
    (header_frame_blobgas_word_reaches s array count input inputLength scratch frame record flag ceiling inputLimit g c (by omega))
  intro next kept remaining
  apply reaches_mono next (decodeHeaderAt 49) (decodeHeaderAt 56) _ _ _ _ (le_refl _) ?_
    (header_fields_at49_frame_reaches next array count input inputLength scratch frame record flag ceiling inputLimit g kept.context remaining)
  intro post framed
  exact kept.trans framed

#print axioms header_fields_at47_frame_reaches

theorem header_fields_at46_frame_reaches {F : Type} (s : PanSemStateFiniteExact 64 F)
    (array count input inputLength scratch frame record flag : BitVec 64) (ceiling inputLimit : Nat)
    (g : HeaderDecoderGeometry array count inputLength scratch frame record flag ceiling inputLimit)
    (c : HeaderDecoderContext s array count input inputLength scratch frame record flag ceiling)
    (budget : 6 * headerDecoderUnitCost inputLimit ≤ s.clock) :
    Reaches s (decodeHeaderAt 46)
      (fun post => HeaderDecoderFrame s post array count input inputLength scratch frame record flag ceiling)
      (6 * headerDecoderUnitCost inputLimit) (decodeHeaderAt 56) := by
  have split : 6 * headerDecoderUnitCost inputLimit =
      1 * headerDecoderUnitCost inputLimit + 5 * headerDecoderUnitCost inputLimit := by omega
  rw [split] at budget ⊢
  apply reaches_trans_budget s (decodeHeaderAt 46) (decodeHeaderAt 47) (decodeHeaderAt 56) _ _
    (1 * headerDecoderUnitCost inputLimit) (5 * headerDecoderUnitCost inputLimit) budget
    (header_frame_blobgas_reaches s array count input inputLength scratch frame record flag ceiling inputLimit g c (by omega))
  intro next kept remaining
  apply reaches_mono next (decodeHeaderAt 47) (decodeHeaderAt 56) _ _ _ _ (le_refl _) ?_
    (header_fields_at47_frame_reaches next array count input inputLength scratch frame record flag ceiling inputLimit g kept.context remaining)
  intro post framed
  exact kept.trans framed

#print axioms header_fields_at46_frame_reaches

theorem header_fields_at44_frame_reaches {F : Type} (s : PanSemStateFiniteExact 64 F)
    (array count input inputLength scratch frame record flag : BitVec 64) (ceiling inputLimit : Nat)
    (g : HeaderDecoderGeometry array count inputLength scratch frame record flag ceiling inputLimit)
    (c : HeaderDecoderContext s array count input inputLength scratch frame record flag ceiling)
    (budget : 7 * headerDecoderUnitCost inputLimit ≤ s.clock) :
    Reaches s (decodeHeaderAt 44)
      (fun post => HeaderDecoderFrame s post array count input inputLength scratch frame record flag ceiling)
      (7 * headerDecoderUnitCost inputLimit) (decodeHeaderAt 56) := by
  have split : 7 * headerDecoderUnitCost inputLimit =
      1 * headerDecoderUnitCost inputLimit + 6 * headerDecoderUnitCost inputLimit := by omega
  rw [split] at budget ⊢
  apply reaches_trans_budget s (decodeHeaderAt 44) (decodeHeaderAt 46) (decodeHeaderAt 56) _ _
    (1 * headerDecoderUnitCost inputLimit) (6 * headerDecoderUnitCost inputLimit) budget
    (header_frame_withdrawals_reaches s array count input inputLength scratch frame record flag ceiling inputLimit g c (by omega))
  intro next kept remaining
  apply reaches_mono next (decodeHeaderAt 46) (decodeHeaderAt 56) _ _ _ _ (le_refl _) ?_
    (header_fields_at46_frame_reaches next array count input inputLength scratch frame record flag ceiling inputLimit g kept.context remaining)
  intro post framed
  exact kept.trans framed

#print axioms header_fields_at44_frame_reaches

theorem header_fields_at42_frame_reaches {F : Type} (s : PanSemStateFiniteExact 64 F)
    (array count input inputLength scratch frame record flag : BitVec 64) (ceiling inputLimit : Nat)
    (g : HeaderDecoderGeometry array count inputLength scratch frame record flag ceiling inputLimit)
    (c : HeaderDecoderContext s array count input inputLength scratch frame record flag ceiling)
    (budget : 8 * headerDecoderUnitCost inputLimit ≤ s.clock) :
    Reaches s (decodeHeaderAt 42)
      (fun post => HeaderDecoderFrame s post array count input inputLength scratch frame record flag ceiling)
      (8 * headerDecoderUnitCost inputLimit) (decodeHeaderAt 56) := by
  have split : 8 * headerDecoderUnitCost inputLimit =
      1 * headerDecoderUnitCost inputLimit + 7 * headerDecoderUnitCost inputLimit := by omega
  rw [split] at budget ⊢
  apply reaches_trans_budget s (decodeHeaderAt 42) (decodeHeaderAt 44) (decodeHeaderAt 56) _ _
    (1 * headerDecoderUnitCost inputLimit) (7 * headerDecoderUnitCost inputLimit) budget
    (header_frame_basefee_reaches s array count input inputLength scratch frame record flag ceiling inputLimit g c (by omega))
  intro next kept remaining
  apply reaches_mono next (decodeHeaderAt 44) (decodeHeaderAt 56) _ _ _ _ (le_refl _) ?_
    (header_fields_at44_frame_reaches next array count input inputLength scratch frame record flag ceiling inputLimit g kept.context remaining)
  intro post framed
  exact kept.trans framed

#print axioms header_fields_at42_frame_reaches

theorem header_fields_at38_frame_reaches {F : Type} (s : PanSemStateFiniteExact 64 F)
    (array count input inputLength scratch frame record flag : BitVec 64) (ceiling inputLimit : Nat)
    (g : HeaderDecoderGeometry array count inputLength scratch frame record flag ceiling inputLimit)
    (c : HeaderDecoderContext s array count input inputLength scratch frame record flag ceiling)
    (budget : 10 * headerDecoderUnitCost inputLimit ≤ s.clock) :
    Reaches s (decodeHeaderAt 38)
      (fun post => HeaderDecoderFrame s post array count input inputLength scratch frame record flag ceiling)
      (10 * headerDecoderUnitCost inputLimit) (decodeHeaderAt 56) := by
  have split : 10 * headerDecoderUnitCost inputLimit =
      2 * headerDecoderUnitCost inputLimit + 8 * headerDecoderUnitCost inputLimit := by omega
  rw [split] at budget ⊢
  apply reaches_trans_budget s (decodeHeaderAt 38) (decodeHeaderAt 42) (decodeHeaderAt 56) _ _
    (2 * headerDecoderUnitCost inputLimit) (8 * headerDecoderUnitCost inputLimit) budget
    (header_frame_middle_bytes_reaches s array count input inputLength scratch frame record flag ceiling inputLimit g c (by omega))
  intro next kept remaining
  apply reaches_mono next (decodeHeaderAt 42) (decodeHeaderAt 56) _ _ _ _ (le_refl _) ?_
    (header_fields_at42_frame_reaches next array count input inputLength scratch frame record flag ceiling inputLimit g kept.context remaining)
  intro post framed
  exact kept.trans framed

#print axioms header_fields_at38_frame_reaches

theorem header_fields_at35_frame_reaches {F : Type} (s : PanSemStateFiniteExact 64 F)
    (array count input inputLength scratch frame record flag : BitVec 64) (ceiling inputLimit : Nat)
    (g : HeaderDecoderGeometry array count inputLength scratch frame record flag ceiling inputLimit)
    (c : HeaderDecoderContext s array count input inputLength scratch frame record flag ceiling)
    (budget : 11 * headerDecoderUnitCost inputLimit ≤ s.clock) :
    Reaches s (decodeHeaderAt 35)
      (fun post => HeaderDecoderFrame s post array count input inputLength scratch frame record flag ceiling)
      (11 * headerDecoderUnitCost inputLimit) (decodeHeaderAt 56) := by
  have split : 11 * headerDecoderUnitCost inputLimit =
      1 * headerDecoderUnitCost inputLimit + 10 * headerDecoderUnitCost inputLimit := by omega
  rw [split] at budget ⊢
  apply reaches_trans_budget s (decodeHeaderAt 35) (decodeHeaderAt 38) (decodeHeaderAt 56) _ _
    (1 * headerDecoderUnitCost inputLimit) (10 * headerDecoderUnitCost inputLimit) budget
    (header_frame_extra_reaches s array count input inputLength scratch frame record flag ceiling inputLimit g c (by omega))
  intro next kept remaining
  apply reaches_mono next (decodeHeaderAt 38) (decodeHeaderAt 56) _ _ _ _ (le_refl _) ?_
    (header_fields_at38_frame_reaches next array count input inputLength scratch frame record flag ceiling inputLimit g kept.context remaining)
  intro post framed
  exact kept.trans framed

#print axioms header_fields_at35_frame_reaches

theorem header_fields_at33_frame_reaches {F : Type} (s : PanSemStateFiniteExact 64 F)
    (array count input inputLength scratch frame record flag : BitVec 64) (ceiling inputLimit : Nat)
    (g : HeaderDecoderGeometry array count inputLength scratch frame record flag ceiling inputLimit)
    (c : HeaderDecoderContext s array count input inputLength scratch frame record flag ceiling)
    (budget : 12 * headerDecoderUnitCost inputLimit ≤ s.clock) :
    Reaches s (decodeHeaderAt 33)
      (fun post => HeaderDecoderFrame s post array count input inputLength scratch frame record flag ceiling)
      (12 * headerDecoderUnitCost inputLimit) (decodeHeaderAt 56) := by
  have split : 12 * headerDecoderUnitCost inputLimit =
      1 * headerDecoderUnitCost inputLimit + 11 * headerDecoderUnitCost inputLimit := by omega
  rw [split] at budget ⊢
  apply reaches_trans_budget s (decodeHeaderAt 33) (decodeHeaderAt 35) (decodeHeaderAt 56) _ _
    (1 * headerDecoderUnitCost inputLimit) (11 * headerDecoderUnitCost inputLimit) budget
    (header_frame_timestamp_word_reaches s array count input inputLength scratch frame record flag ceiling inputLimit g c (by omega))
  intro next kept remaining
  apply reaches_mono next (decodeHeaderAt 35) (decodeHeaderAt 56) _ _ _ _ (le_refl _) ?_
    (header_fields_at35_frame_reaches next array count input inputLength scratch frame record flag ceiling inputLimit g kept.context remaining)
  intro post framed
  exact kept.trans framed

#print axioms header_fields_at33_frame_reaches

theorem header_fields_at31_frame_reaches {F : Type} (s : PanSemStateFiniteExact 64 F)
    (array count input inputLength scratch frame record flag : BitVec 64) (ceiling inputLimit : Nat)
    (g : HeaderDecoderGeometry array count inputLength scratch frame record flag ceiling inputLimit)
    (c : HeaderDecoderContext s array count input inputLength scratch frame record flag ceiling)
    (budget : 13 * headerDecoderUnitCost inputLimit ≤ s.clock) :
    Reaches s (decodeHeaderAt 31)
      (fun post => HeaderDecoderFrame s post array count input inputLength scratch frame record flag ceiling)
      (13 * headerDecoderUnitCost inputLimit) (decodeHeaderAt 56) := by
  have split : 13 * headerDecoderUnitCost inputLimit =
      1 * headerDecoderUnitCost inputLimit + 12 * headerDecoderUnitCost inputLimit := by omega
  rw [split] at budget ⊢
  apply reaches_trans_budget s (decodeHeaderAt 31) (decodeHeaderAt 33) (decodeHeaderAt 56) _ _
    (1 * headerDecoderUnitCost inputLimit) (12 * headerDecoderUnitCost inputLimit) budget
    (header_frame_timestamp_reaches s array count input inputLength scratch frame record flag ceiling inputLimit g c (by omega))
  intro next kept remaining
  apply reaches_mono next (decodeHeaderAt 33) (decodeHeaderAt 56) _ _ _ _ (le_refl _) ?_
    (header_fields_at33_frame_reaches next array count input inputLength scratch frame record flag ceiling inputLimit g kept.context remaining)
  intro post framed
  exact kept.trans framed

#print axioms header_fields_at31_frame_reaches

theorem header_fields_at27_frame_reaches {F : Type} (s : PanSemStateFiniteExact 64 F)
    (array count input inputLength scratch frame record flag : BitVec 64) (ceiling inputLimit : Nat)
    (g : HeaderDecoderGeometry array count inputLength scratch frame record flag ceiling inputLimit)
    (c : HeaderDecoderContext s array count input inputLength scratch frame record flag ceiling)
    (budget : 15 * headerDecoderUnitCost inputLimit ≤ s.clock) :
    Reaches s (decodeHeaderAt 27)
      (fun post => HeaderDecoderFrame s post array count input inputLength scratch frame record flag ceiling)
      (15 * headerDecoderUnitCost inputLimit) (decodeHeaderAt 56) := by
  have split : 15 * headerDecoderUnitCost inputLimit =
      2 * headerDecoderUnitCost inputLimit + 13 * headerDecoderUnitCost inputLimit := by omega
  rw [split] at budget ⊢
  apply reaches_trans_budget s (decodeHeaderAt 27) (decodeHeaderAt 31) (decodeHeaderAt 56) _ _
    (2 * headerDecoderUnitCost inputLimit) (13 * headerDecoderUnitCost inputLimit) budget
    (header_frame_words_reaches s array count input inputLength scratch frame record flag ceiling inputLimit g c (by omega))
  intro next kept remaining
  apply reaches_mono next (decodeHeaderAt 31) (decodeHeaderAt 56) _ _ _ _ (le_refl _) ?_
    (header_fields_at31_frame_reaches next array count input inputLength scratch frame record flag ceiling inputLimit g kept.context remaining)
  intro post framed
  exact kept.trans framed

#print axioms header_fields_at27_frame_reaches

theorem header_fields_at25_frame_reaches {F : Type} (s : PanSemStateFiniteExact 64 F)
    (array count input inputLength scratch frame record flag : BitVec 64) (ceiling inputLimit : Nat)
    (g : HeaderDecoderGeometry array count inputLength scratch frame record flag ceiling inputLimit)
    (c : HeaderDecoderContext s array count input inputLength scratch frame record flag ceiling)
    (budget : 16 * headerDecoderUnitCost inputLimit ≤ s.clock) :
    Reaches s (decodeHeaderAt 25)
      (fun post => HeaderDecoderFrame s post array count input inputLength scratch frame record flag ceiling)
      (16 * headerDecoderUnitCost inputLimit) (decodeHeaderAt 56) := by
  have split : 16 * headerDecoderUnitCost inputLimit =
      1 * headerDecoderUnitCost inputLimit + 15 * headerDecoderUnitCost inputLimit := by omega
  rw [split] at budget ⊢
  apply reaches_trans_budget s (decodeHeaderAt 25) (decodeHeaderAt 27) (decodeHeaderAt 56) _ _
    (1 * headerDecoderUnitCost inputLimit) (15 * headerDecoderUnitCost inputLimit) budget
    (header_frame_word_reaches s array count input inputLength scratch frame record flag ceiling inputLimit g c (by omega))
  intro next kept remaining
  apply reaches_mono next (decodeHeaderAt 27) (decodeHeaderAt 56) _ _ _ _ (le_refl _) ?_
    (header_fields_at27_frame_reaches next array count input inputLength scratch frame record flag ceiling inputLimit g kept.context remaining)
  intro post framed
  exact kept.trans framed

#print axioms header_fields_at25_frame_reaches

theorem header_fields_at23_frame_reaches {F : Type} (s : PanSemStateFiniteExact 64 F)
    (array count input inputLength scratch frame record flag : BitVec 64) (ceiling inputLimit : Nat)
    (g : HeaderDecoderGeometry array count inputLength scratch frame record flag ceiling inputLimit)
    (c : HeaderDecoderContext s array count input inputLength scratch frame record flag ceiling)
    (budget : 17 * headerDecoderUnitCost inputLimit ≤ s.clock) :
    Reaches s (decodeHeaderAt 23)
      (fun post => HeaderDecoderFrame s post array count input inputLength scratch frame record flag ceiling)
      (17 * headerDecoderUnitCost inputLimit) (decodeHeaderAt 56) := by
  have split : 17 * headerDecoderUnitCost inputLimit =
      1 * headerDecoderUnitCost inputLimit + 16 * headerDecoderUnitCost inputLimit := by omega
  rw [split] at budget ⊢
  apply reaches_trans_budget s (decodeHeaderAt 23) (decodeHeaderAt 25) (decodeHeaderAt 56) _ _
    (1 * headerDecoderUnitCost inputLimit) (16 * headerDecoderUnitCost inputLimit) budget
    (header_frame_difficulty_reaches s array count input inputLength scratch frame record flag ceiling inputLimit g c (by omega))
  intro next kept remaining
  apply reaches_mono next (decodeHeaderAt 25) (decodeHeaderAt 56) _ _ _ _ (le_refl _) ?_
    (header_fields_at25_frame_reaches next array count input inputLength scratch frame record flag ceiling inputLimit g kept.context remaining)
  intro post framed
  exact kept.trans framed

#print axioms header_fields_at23_frame_reaches

theorem header_fields_at11_frame_reaches {F : Type} (s : PanSemStateFiniteExact 64 F)
    (array count input inputLength scratch frame record flag : BitVec 64) (ceiling inputLimit : Nat)
    (g : HeaderDecoderGeometry array count inputLength scratch frame record flag ceiling inputLimit)
    (c : HeaderDecoderContext s array count input inputLength scratch frame record flag ceiling)
    (budget : 23 * headerDecoderUnitCost inputLimit ≤ s.clock) :
    Reaches s (decodeHeaderAt 11)
      (fun post => HeaderDecoderFrame s post array count input inputLength scratch frame record flag ceiling)
      (23 * headerDecoderUnitCost inputLimit) (decodeHeaderAt 56) := by
  have split : 23 * headerDecoderUnitCost inputLimit =
      6 * headerDecoderUnitCost inputLimit + 17 * headerDecoderUnitCost inputLimit := by omega
  rw [split] at budget ⊢
  apply reaches_trans_budget s (decodeHeaderAt 11) (decodeHeaderAt 23) (decodeHeaderAt 56) _ _
    (6 * headerDecoderUnitCost inputLimit) (17 * headerDecoderUnitCost inputLimit) budget
    (header_frame_bytes_reaches s array count input inputLength scratch frame record flag ceiling inputLimit g c (by omega))
  intro next kept remaining
  apply reaches_mono next (decodeHeaderAt 23) (decodeHeaderAt 56) _ _ _ _ (le_refl _) ?_
    (header_fields_at23_frame_reaches next array count input inputLength scratch frame record flag ceiling inputLimit g kept.context remaining)
  intro post framed
  exact kept.trans framed

#print axioms header_fields_at11_frame_reaches

theorem header_fields_at9_frame_reaches {F : Type} (s : PanSemStateFiniteExact 64 F)
    (array count input inputLength scratch frame record flag : BitVec 64) (ceiling inputLimit : Nat)
    (g : HeaderDecoderGeometry array count inputLength scratch frame record flag ceiling inputLimit)
    (c : HeaderDecoderContext s array count input inputLength scratch frame record flag ceiling)
    (budget : 24 * headerDecoderUnitCost inputLimit ≤ s.clock) :
    Reaches s (decodeHeaderAt 9)
      (fun post => HeaderDecoderFrame s post array count input inputLength scratch frame record flag ceiling)
      (24 * headerDecoderUnitCost inputLimit) (decodeHeaderAt 56) := by
  have split : 24 * headerDecoderUnitCost inputLimit =
      1 * headerDecoderUnitCost inputLimit + 23 * headerDecoderUnitCost inputLimit := by omega
  rw [split] at budget ⊢
  apply reaches_trans_budget s (decodeHeaderAt 9) (decodeHeaderAt 11) (decodeHeaderAt 56) _ _
    (1 * headerDecoderUnitCost inputLimit) (23 * headerDecoderUnitCost inputLimit) budget
    (header_frame_first_reaches s array count input inputLength scratch frame record flag ceiling inputLimit g c (by omega))
  intro next kept remaining
  apply reaches_mono next (decodeHeaderAt 11) (decodeHeaderAt 56) _ _ _ _ (le_refl _) ?_
    (header_fields_at11_frame_reaches next array count input inputLength scratch frame record flag ceiling inputLimit g kept.context remaining)
  intro post framed
  exact kept.trans framed

#print axioms header_fields_at9_frame_reaches

end InitECandidate.Runtime
