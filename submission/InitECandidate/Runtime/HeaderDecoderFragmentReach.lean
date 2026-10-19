import InitECandidate.Runtime.HeaderDecoderContext
import InitECandidate.Runtime.DecodeHeaderFirstFieldStoreReach
import InitECandidate.Runtime.DecodeHeaderEarlyBytesReach
import InitECandidate.Runtime.DecodeHeaderDifficultyReach
import InitECandidate.Runtime.DecodeHeaderFirstWordReach
import InitECandidate.Runtime.DecodeHeaderEarlyWordsReach
import InitECandidate.Runtime.DecodeHeaderTimestampEntryReach
import InitECandidate.Runtime.DecodeHeaderTimestampWordReach
import InitECandidate.Runtime.DecodeHeaderMiddleBytesReach
import InitECandidate.Runtime.DecodeHeaderBasefeeReach
import InitECandidate.Runtime.DecodeHeaderWithdrawalsBytesReach
import InitECandidate.Runtime.DecodeHeaderBlobGasFieldReach
import InitECandidate.Runtime.DecodeHeaderBlobGasWordReach
import InitECandidate.Runtime.DecodeHeaderExcessBlobGasFieldReach
import InitECandidate.Runtime.DecodeHeaderExcessBlobGasWordReach
import InitECandidate.Runtime.DecodeHeaderLastBytesReach
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
set_option maxRecDepth 100000
set_option maxHeartbeats 200000

def headerDecoderUnitCost (limit : Nat) : Nat := headerRlpFieldCost limit + 35

theorem header_context_first_reaches {F : Type} (s : PanSemStateFiniteExact 64 F)
    (array count input inputLength scratch frame record flag : BitVec 64) (ceiling inputLimit : Nat)
    (g : HeaderDecoderGeometry array count inputLength scratch frame record flag ceiling inputLimit)
    (c : HeaderDecoderContext s array count input inputLength scratch frame record flag ceiling)
    (budget : 1 * headerDecoderUnitCost inputLimit ≤ s.clock) :
    Reaches s (decodeHeaderAt 9)
      (fun post => HeaderDecoderContext post array count input inputLength scratch frame record flag ceiling)
      (1 * headerDecoderUnitCost inputLimit) (decodeHeaderAt 11) := by
  have cb := g.countBound
  have reached := decode_header_first_field_store_reaches s array count input inputLength scratch frame record ceiling inputLimit c.atArray c.atRecord g.before g.recordFits c.table (by omega) g.above g.fits g.inputBound g.limitBound c.scratchGlobal c.frameGlobal c.code g.orderedFrame g.framePositive g.scratchBelow c.arena (by unfold headerDecoderUnitCost at budget; omega)
  apply reaches_mono s (decodeHeaderAt 9) (decodeHeaderAt 11) _ _ _ _ (by unfold headerDecoderUnitCost; omega) ?_ reached
  intro post facts
  obtain ⟨word,locals,table,domain,installed,globals,memory⟩ := facts
  exact c.after_update (ofString "f") _ (by decide) locals table domain installed globals

#print axioms header_context_first_reaches

theorem header_context_bytes_reaches {F : Type} (s : PanSemStateFiniteExact 64 F)
    (array count input inputLength scratch frame record flag : BitVec 64) (ceiling inputLimit : Nat)
    (g : HeaderDecoderGeometry array count inputLength scratch frame record flag ceiling inputLimit)
    (c : HeaderDecoderContext s array count input inputLength scratch frame record flag ceiling)
    (budget : 6 * headerDecoderUnitCost inputLimit ≤ s.clock) :
    Reaches s (decodeHeaderAt 11)
      (fun post => HeaderDecoderContext post array count input inputLength scratch frame record flag ceiling)
      (6 * headerDecoderUnitCost inputLimit) (decodeHeaderAt 23) := by
  have cb := g.countBound
  have reached := decode_header_early_bytes_reaches s array count input inputLength scratch frame record ceiling inputLimit (by omega) c.atArray c.atRecord g.before g.recordFits c.table g.above g.fits g.inputBound g.limitBound c.scratchGlobal c.frameGlobal c.code g.orderedFrame g.framePositive g.scratchBelow c.arena (by unfold headerDecoderUnitCost at budget; omega)
  apply reaches_mono s (decodeHeaderAt 11) (decodeHeaderAt 23) _ _ _ _ (by unfold headerDecoderUnitCost; omega) ?_ reached
  intro post facts
  apply c.after_frame facts.table ?_ facts.domain facts.code facts.globals
  intro name important
  apply facts.locals name
  rcases important with rfl | rfl | rfl <;> decide

#print axioms header_context_bytes_reaches

theorem header_context_difficulty_reaches {F : Type} (s : PanSemStateFiniteExact 64 F)
    (array count input inputLength scratch frame record flag : BitVec 64) (ceiling inputLimit : Nat)
    (g : HeaderDecoderGeometry array count inputLength scratch frame record flag ceiling inputLimit)
    (c : HeaderDecoderContext s array count input inputLength scratch frame record flag ceiling)
    (budget : 1 * headerDecoderUnitCost inputLimit ≤ s.clock) :
    Reaches s (decodeHeaderAt 23)
      (fun post => HeaderDecoderContext post array count input inputLength scratch frame record flag ceiling)
      (1 * headerDecoderUnitCost inputLimit) (decodeHeaderAt 25) := by
  have cb := g.countBound
  have reached := decode_header_difficulty_reaches s array count input inputLength scratch frame record ceiling inputLimit c.atArray c.atRecord g.before g.recordFits c.table (by omega) g.above g.fits g.inputBound g.limitBound c.scratchGlobal c.frameGlobal c.code g.orderedFrame g.framePositive g.scratchBelow c.arena (by unfold headerDecoderUnitCost at budget; omega)
  apply reaches_mono s (decodeHeaderAt 23) (decodeHeaderAt 25) _ _ _ _ (by unfold headerDecoderUnitCost; omega) ?_ reached
  intro post facts
  obtain ⟨first,second,third,fourth,locals,table,domain,installed,globals,memory⟩ := facts
  exact c.after_update (ofString "d") _ (by decide) locals table domain installed globals

#print axioms header_context_difficulty_reaches

theorem header_context_word_reaches {F : Type} (s : PanSemStateFiniteExact 64 F)
    (array count input inputLength scratch frame record flag : BitVec 64) (ceiling inputLimit : Nat)
    (g : HeaderDecoderGeometry array count inputLength scratch frame record flag ceiling inputLimit)
    (c : HeaderDecoderContext s array count input inputLength scratch frame record flag ceiling)
    (budget : 1 * headerDecoderUnitCost inputLimit ≤ s.clock) :
    Reaches s (decodeHeaderAt 25)
      (fun post => HeaderDecoderContext post array count input inputLength scratch frame record flag ceiling)
      (1 * headerDecoderUnitCost inputLimit) (decodeHeaderAt 27) := by
  have cb := g.countBound
  have reached := decode_header_first_word_reaches s array count input inputLength scratch frame record ceiling inputLimit c.atArray c.atRecord g.before g.recordFits c.table (by omega) g.above g.fits g.inputBound g.limitBound c.scratchGlobal c.frameGlobal c.code g.orderedFrame g.framePositive g.scratchBelow c.arena (by unfold headerDecoderUnitCost at budget; omega)
  apply reaches_mono s (decodeHeaderAt 25) (decodeHeaderAt 27) _ _ _ _ (by unfold headerDecoderUnitCost; omega) ?_ reached
  intro post facts
  obtain ⟨word,locals,table,domain,installed,globals,memory⟩ := facts
  exact c.after_update (ofString "w") _ (by decide) locals table domain installed globals

#print axioms header_context_word_reaches

theorem header_context_words_reaches {F : Type} (s : PanSemStateFiniteExact 64 F)
    (array count input inputLength scratch frame record flag : BitVec 64) (ceiling inputLimit : Nat)
    (g : HeaderDecoderGeometry array count inputLength scratch frame record flag ceiling inputLimit)
    (c : HeaderDecoderContext s array count input inputLength scratch frame record flag ceiling)
    (budget : 2 * headerDecoderUnitCost inputLimit ≤ s.clock) :
    Reaches s (decodeHeaderAt 27)
      (fun post => HeaderDecoderContext post array count input inputLength scratch frame record flag ceiling)
      (2 * headerDecoderUnitCost inputLimit) (decodeHeaderAt 31) := by
  have cb := g.countBound
  have reached := decode_header_early_words_reaches s array count input inputLength scratch frame record ceiling inputLimit (by omega) c.atArray c.atRecord g.before g.recordFits c.table g.above g.fits g.inputBound g.limitBound c.scratchGlobal c.frameGlobal c.code g.orderedFrame g.framePositive g.scratchBelow c.arena (by unfold headerDecoderUnitCost at budget; omega)
  apply reaches_mono s (decodeHeaderAt 27) (decodeHeaderAt 31) _ _ _ _ (by unfold headerDecoderUnitCost; omega) ?_ reached
  intro post facts
  apply c.after_frame facts.table ?_ facts.domain facts.code facts.globals
  intro name important
  apply facts.locals name
  rcases important with rfl | rfl | rfl <;> decide

#print axioms header_context_words_reaches

theorem header_context_timestamp_reaches {F : Type} (s : PanSemStateFiniteExact 64 F)
    (array count input inputLength scratch frame record flag : BitVec 64) (ceiling inputLimit : Nat)
    (g : HeaderDecoderGeometry array count inputLength scratch frame record flag ceiling inputLimit)
    (c : HeaderDecoderContext s array count input inputLength scratch frame record flag ceiling)
    (budget : 1 * headerDecoderUnitCost inputLimit ≤ s.clock) :
    Reaches s (decodeHeaderAt 31)
      (fun post => HeaderDecoderContext post array count input inputLength scratch frame record flag ceiling)
      (1 * headerDecoderUnitCost inputLimit) (decodeHeaderAt 33) := by
  have cb := g.countBound
  have reached := decode_header_timestamp_entry_reaches s array count input inputLength scratch frame ceiling inputLimit c.atArray c.table (by omega) g.above g.fits g.inputBound g.limitBound c.scratchGlobal c.frameGlobal c.code g.orderedFrame g.framePositive g.scratchBelow c.arena (by unfold headerDecoderUnitCost at budget; omega)
  apply reaches_mono s (decodeHeaderAt 31) (decodeHeaderAt 33) _ _ _ _ (by unfold headerDecoderUnitCost; omega) ?_ reached
  intro post facts
  obtain ⟨value,locals,checked,table,domain,installed,globals,memory⟩ := facts
  exact c.after_update (ofString "tsf") _ (by decide) locals table domain installed globals

#print axioms header_context_timestamp_reaches

theorem header_context_timestamp_word_reaches {F : Type} (s : PanSemStateFiniteExact 64 F)
    (array count input inputLength scratch frame record flag : BitVec 64) (ceiling inputLimit : Nat)
    (g : HeaderDecoderGeometry array count inputLength scratch frame record flag ceiling inputLimit)
    (c : HeaderDecoderContext s array count input inputLength scratch frame record flag ceiling)
    (budget : 1 * headerDecoderUnitCost inputLimit ≤ s.clock) :
    Reaches s (decodeHeaderAt 33)
      (fun post => HeaderDecoderContext post array count input inputLength scratch frame record flag ceiling)
      (1 * headerDecoderUnitCost inputLimit) (decodeHeaderAt 35) := by
  have cb := g.countBound
  have reached := decode_header_timestamp_word_reaches s array count input inputLength scratch frame record ceiling inputLimit (by omega) c.atArray c.atRecord g.before g.recordFits c.table g.above g.fits g.inputBound g.limitBound c.scratchGlobal c.frameGlobal c.code g.orderedFrame g.framePositive g.scratchBelow c.arena (by unfold headerDecoderUnitCost at budget; omega)
  apply reaches_mono s (decodeHeaderAt 33) (decodeHeaderAt 35) _ _ _ _ (by unfold headerDecoderUnitCost; omega) ?_ reached
  intro post facts
  apply c.after_frame facts.table ?_ facts.domain facts.code facts.globals
  intro name important
  apply facts.locals name
  rcases important with rfl | rfl | rfl <;> decide

#print axioms header_context_timestamp_word_reaches

theorem header_context_middle_bytes_reaches {F : Type} (s : PanSemStateFiniteExact 64 F)
    (array count input inputLength scratch frame record flag : BitVec 64) (ceiling inputLimit : Nat)
    (g : HeaderDecoderGeometry array count inputLength scratch frame record flag ceiling inputLimit)
    (c : HeaderDecoderContext s array count input inputLength scratch frame record flag ceiling)
    (budget : 2 * headerDecoderUnitCost inputLimit ≤ s.clock) :
    Reaches s (decodeHeaderAt 38)
      (fun post => HeaderDecoderContext post array count input inputLength scratch frame record flag ceiling)
      (2 * headerDecoderUnitCost inputLimit) (decodeHeaderAt 42) := by
  have cb := g.countBound
  have reached := decode_header_middle_bytes_reaches s array count input inputLength scratch frame record ceiling inputLimit (by omega) c.atArray c.atRecord g.before g.recordFits c.table g.above g.fits g.inputBound g.limitBound c.scratchGlobal c.frameGlobal c.code g.orderedFrame g.framePositive g.scratchBelow c.arena (by unfold headerDecoderUnitCost at budget; omega)
  apply reaches_mono s (decodeHeaderAt 38) (decodeHeaderAt 42) _ _ _ _ (by unfold headerDecoderUnitCost; omega) ?_ reached
  intro post facts
  apply c.after_frame facts.table ?_ facts.domain facts.code facts.globals
  intro name important
  apply facts.locals name
  rcases important with rfl | rfl | rfl <;> decide

#print axioms header_context_middle_bytes_reaches

theorem header_context_basefee_reaches {F : Type} (s : PanSemStateFiniteExact 64 F)
    (array count input inputLength scratch frame record flag : BitVec 64) (ceiling inputLimit : Nat)
    (g : HeaderDecoderGeometry array count inputLength scratch frame record flag ceiling inputLimit)
    (c : HeaderDecoderContext s array count input inputLength scratch frame record flag ceiling)
    (budget : 1 * headerDecoderUnitCost inputLimit ≤ s.clock) :
    Reaches s (decodeHeaderAt 42)
      (fun post => HeaderDecoderContext post array count input inputLength scratch frame record flag ceiling)
      (1 * headerDecoderUnitCost inputLimit) (decodeHeaderAt 44) := by
  have cb := g.countBound
  have reached := decode_header_basefee_reaches s array count input inputLength scratch frame record ceiling inputLimit c.atArray c.atRecord g.before g.recordFits c.table (by omega) g.above g.fits g.inputBound g.limitBound c.scratchGlobal c.frameGlobal c.code g.orderedFrame g.framePositive g.scratchBelow c.arena (by unfold headerDecoderUnitCost at budget; omega)
  apply reaches_mono s (decodeHeaderAt 42) (decodeHeaderAt 44) _ _ _ _ (by unfold headerDecoderUnitCost; omega) ?_ reached
  intro post facts
  obtain ⟨first,second,third,fourth,locals,table,domain,installed,globals,memory⟩ := facts
  exact c.after_update (ofString "d") _ (by decide) locals table domain installed globals

#print axioms header_context_basefee_reaches

theorem header_context_withdrawals_reaches {F : Type} (s : PanSemStateFiniteExact 64 F)
    (array count input inputLength scratch frame record flag : BitVec 64) (ceiling inputLimit : Nat)
    (g : HeaderDecoderGeometry array count inputLength scratch frame record flag ceiling inputLimit)
    (c : HeaderDecoderContext s array count input inputLength scratch frame record flag ceiling)
    (budget : 1 * headerDecoderUnitCost inputLimit ≤ s.clock) :
    Reaches s (decodeHeaderAt 44)
      (fun post => HeaderDecoderContext post array count input inputLength scratch frame record flag ceiling)
      (1 * headerDecoderUnitCost inputLimit) (decodeHeaderAt 46) := by
  have cb := g.countBound
  have reached := decode_header_withdrawals_bytes_reaches s array count input inputLength scratch frame record ceiling inputLimit (by omega) c.atArray c.atRecord g.before g.recordFits c.table g.above g.fits g.inputBound g.limitBound c.scratchGlobal c.frameGlobal c.code g.orderedFrame g.framePositive g.scratchBelow c.arena (by unfold headerDecoderUnitCost at budget; omega)
  apply reaches_mono s (decodeHeaderAt 44) (decodeHeaderAt 46) _ _ _ _ (by unfold headerDecoderUnitCost; omega) ?_ reached
  intro post facts
  apply c.after_frame facts.table ?_ facts.domain facts.code facts.globals
  intro name important
  apply facts.locals name
  rcases important with rfl | rfl | rfl <;> decide

#print axioms header_context_withdrawals_reaches

theorem header_context_blobgas_reaches {F : Type} (s : PanSemStateFiniteExact 64 F)
    (array count input inputLength scratch frame record flag : BitVec 64) (ceiling inputLimit : Nat)
    (g : HeaderDecoderGeometry array count inputLength scratch frame record flag ceiling inputLimit)
    (c : HeaderDecoderContext s array count input inputLength scratch frame record flag ceiling)
    (budget : 1 * headerDecoderUnitCost inputLimit ≤ s.clock) :
    Reaches s (decodeHeaderAt 46)
      (fun post => HeaderDecoderContext post array count input inputLength scratch frame record flag ceiling)
      (1 * headerDecoderUnitCost inputLimit) (decodeHeaderAt 47) := by
  have cb := g.countBound
  have reached := decode_header_blobgas_field_reaches s array count input inputLength scratch frame ceiling inputLimit c.atArray c.table (by omega) g.above g.fits g.inputBound g.limitBound c.scratchGlobal c.frameGlobal c.code g.orderedFrame g.framePositive g.scratchBelow c.arena (by unfold headerDecoderUnitCost at budget; omega)
  apply reaches_mono s (decodeHeaderAt 46) (decodeHeaderAt 47) _ _ _ _ (by unfold headerDecoderUnitCost; omega) ?_ reached
  intro post facts
  obtain ⟨value,locals,checked,table,domain,installed,globals,memory⟩ := facts
  exact c.after_update (ofString "bg") _ (by decide) locals table domain installed globals

#print axioms header_context_blobgas_reaches

theorem header_context_blobgas_word_reaches {F : Type} (s : PanSemStateFiniteExact 64 F)
    (array count input inputLength scratch frame record flag : BitVec 64) (ceiling inputLimit : Nat)
    (g : HeaderDecoderGeometry array count inputLength scratch frame record flag ceiling inputLimit)
    (c : HeaderDecoderContext s array count input inputLength scratch frame record flag ceiling)
    (budget : 1 * headerDecoderUnitCost inputLimit ≤ s.clock) :
    Reaches s (decodeHeaderAt 47)
      (fun post => HeaderDecoderContext post array count input inputLength scratch frame record flag ceiling)
      (1 * headerDecoderUnitCost inputLimit) (decodeHeaderAt 49) := by
  have cb := g.countBound
  have reached := decode_header_blobgas_word_reaches s array count input inputLength scratch frame record ceiling inputLimit (by omega) c.atArray c.atRecord g.before g.recordFits c.table g.above g.fits g.inputBound g.limitBound c.scratchGlobal c.frameGlobal c.code g.orderedFrame g.framePositive g.scratchBelow c.arena (by unfold headerDecoderUnitCost at budget; omega)
  apply reaches_mono s (decodeHeaderAt 47) (decodeHeaderAt 49) _ _ _ _ (by unfold headerDecoderUnitCost; omega) ?_ reached
  intro post facts
  apply c.after_frame facts.table ?_ facts.domain facts.code facts.globals
  intro name important
  apply facts.locals name
  rcases important with rfl | rfl | rfl <;> decide

#print axioms header_context_blobgas_word_reaches

theorem header_context_excess_blobgas_reaches {F : Type} (s : PanSemStateFiniteExact 64 F)
    (array count input inputLength scratch frame record flag : BitVec 64) (ceiling inputLimit : Nat)
    (g : HeaderDecoderGeometry array count inputLength scratch frame record flag ceiling inputLimit)
    (c : HeaderDecoderContext s array count input inputLength scratch frame record flag ceiling)
    (budget : 1 * headerDecoderUnitCost inputLimit ≤ s.clock) :
    Reaches s (decodeHeaderAt 49)
      (fun post => HeaderDecoderContext post array count input inputLength scratch frame record flag ceiling)
      (1 * headerDecoderUnitCost inputLimit) (decodeHeaderAt 50) := by
  have cb := g.countBound
  have reached := decode_header_excess_blobgas_field_reaches s array count input inputLength scratch frame ceiling inputLimit c.atArray c.table (by omega) g.above g.fits g.inputBound g.limitBound c.scratchGlobal c.frameGlobal c.code g.orderedFrame g.framePositive g.scratchBelow c.arena (by unfold headerDecoderUnitCost at budget; omega)
  apply reaches_mono s (decodeHeaderAt 49) (decodeHeaderAt 50) _ _ _ _ (by unfold headerDecoderUnitCost; omega) ?_ reached
  intro post facts
  obtain ⟨value,locals,checked,table,domain,installed,globals,memory⟩ := facts
  exact c.after_update (ofString "bg") _ (by decide) locals table domain installed globals

#print axioms header_context_excess_blobgas_reaches

theorem header_context_excess_blobgas_word_reaches {F : Type} (s : PanSemStateFiniteExact 64 F)
    (array count input inputLength scratch frame record flag : BitVec 64) (ceiling inputLimit : Nat)
    (g : HeaderDecoderGeometry array count inputLength scratch frame record flag ceiling inputLimit)
    (c : HeaderDecoderContext s array count input inputLength scratch frame record flag ceiling)
    (budget : 1 * headerDecoderUnitCost inputLimit ≤ s.clock) :
    Reaches s (decodeHeaderAt 50)
      (fun post => HeaderDecoderContext post array count input inputLength scratch frame record flag ceiling)
      (1 * headerDecoderUnitCost inputLimit) (decodeHeaderAt 52) := by
  have cb := g.countBound
  have reached := decode_header_excess_blobgas_word_reaches s array count input inputLength scratch frame record ceiling inputLimit (by omega) c.atArray c.atRecord g.before g.recordFits c.table g.above g.fits g.inputBound g.limitBound c.scratchGlobal c.frameGlobal c.code g.orderedFrame g.framePositive g.scratchBelow c.arena (by unfold headerDecoderUnitCost at budget; omega)
  apply reaches_mono s (decodeHeaderAt 50) (decodeHeaderAt 52) _ _ _ _ (by unfold headerDecoderUnitCost; omega) ?_ reached
  intro post facts
  apply c.after_frame facts.table ?_ facts.domain facts.code facts.globals
  intro name important
  apply facts.locals name
  rcases important with rfl | rfl | rfl <;> decide

#print axioms header_context_excess_blobgas_word_reaches

theorem header_context_last_bytes_reaches {F : Type} (s : PanSemStateFiniteExact 64 F)
    (array count input inputLength scratch frame record flag : BitVec 64) (ceiling inputLimit : Nat)
    (g : HeaderDecoderGeometry array count inputLength scratch frame record flag ceiling inputLimit)
    (c : HeaderDecoderContext s array count input inputLength scratch frame record flag ceiling)
    (budget : 2 * headerDecoderUnitCost inputLimit ≤ s.clock) :
    Reaches s (decodeHeaderAt 52)
      (fun post => HeaderDecoderContext post array count input inputLength scratch frame record flag ceiling)
      (2 * headerDecoderUnitCost inputLimit) (decodeHeaderAt 56) := by
  have cb := g.countBound
  have reached := decode_header_last_bytes_reaches s array count input inputLength scratch frame record ceiling inputLimit (by omega) c.atArray c.atRecord g.before g.recordFits c.table g.above g.fits g.inputBound g.limitBound c.scratchGlobal c.frameGlobal c.code g.orderedFrame g.framePositive g.scratchBelow c.arena (by unfold headerDecoderUnitCost at budget; omega)
  apply reaches_mono s (decodeHeaderAt 52) (decodeHeaderAt 56) _ _ _ _ (by unfold headerDecoderUnitCost; omega) ?_ reached
  intro post facts
  apply c.after_frame facts.table ?_ facts.domain facts.code facts.globals
  intro name important
  apply facts.locals name
  rcases important with rfl | rfl | rfl <;> decide

#print axioms header_context_last_bytes_reaches

end InitECandidate.Runtime
