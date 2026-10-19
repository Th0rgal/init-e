import InitECandidate.Runtime.DecodeHeaderExtraFieldReach
import InitECandidate.Runtime.HeaderExpressionStoreReach
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
set_option maxRecDepth 100000

theorem source_decode_header_extra_pointer_store : decodeHeaderAt 36 =
    .seq (headerExpressionStore (.rfield 0 (.var .local (ofString "ex"))) 128) (decodeHeaderAt 37) := rfl

theorem source_decode_header_extra_length_store : decodeHeaderAt 37 =
    .seq (headerExpressionStore (.rfield 1 (.var .local (ofString "ex"))) 136) (decodeHeaderAt 38) := rfl

/-- The actual two extra-data record stores project the checked pair and keep
the older readable slice table, or terminate without spending source clock. -/
theorem decode_header_extra_stores_reaches {F : Type} (s : PanSemStateFiniteExact 64 F)
    (array count input inputLength record pointer length : BitVec 64)
    (code : s.code = originalRuntimeCode)
    (atRecord : s.locals.lookup (ofString "h") = some (.val (.word record)))
    (atExtra : s.locals.lookup (ofString "ex") = some (.rStruct [.val (.word pointer),.val (.word length)]))
    (recordFits : record.toNat + 248 < 2^64)
    (table : RlpSliceInputPrefix s array input inputLength count.toNat)
    (before : array.toNat + count.toNat * 16 ≤ record.toNat) :
    Reaches s (decodeHeaderAt 36)
      (fun post => RlpSliceInputPrefix post array input inputLength count.toNat ∧
        post.locals = s.locals ∧ post.globals = s.globals ∧ post.memaddrs = s.memaddrs ∧ post.code = s.code ∧
        (∀ address : BitVec 64, address.toNat < record.toNat → post.memory address = s.memory address))
      0 (decodeHeaderAt 38) := by
  have first := header_expression_store_reaches s array count input inputLength record pointer 128
    (.rfield 0 (.var .local (ofString "ex"))) (decodeHeaderAt 37) code atRecord
    (by simp [evalHOLExact,atExtra]) (by decide) recordFits table before
  rw [source_decode_header_extra_pointer_store]
  apply reaches_trans s _ (decodeHeaderAt 37) (decodeHeaderAt 38) _ _ 0 0 first
  intro stored facts
  obtain ⟨tableStored,locals,globals,domain,installed,memory⟩ := facts
  have atRecordStored : stored.locals.lookup (ofString "h") = some (.val (.word record)) := by
    rw [locals]; exact atRecord
  have atExtraStored : stored.locals.lookup (ofString "ex") = some (.rStruct [.val (.word pointer),.val (.word length)]) := by
    rw [locals]; exact atExtra
  have second := header_expression_store_reaches stored array count input inputLength record length 136
    (.rfield 1 (.var .local (ofString "ex"))) (decodeHeaderAt 38) (installed.trans code) atRecordStored
    (by simp [evalHOLExact,atExtraStored]) (by decide) recordFits tableStored before
  rw [source_decode_header_extra_length_store]
  apply reaches_mono stored _ (decodeHeaderAt 38) _ _ 0 0 (le_refl _) ?_ second
  intro post kept
  obtain ⟨tablePost,localsPost,globalsPost,domainPost,codePost,memoryPost⟩ := kept
  exact ⟨tablePost,localsPost.trans locals,globalsPost.trans globals,domainPost.trans domain,codePost.trans installed,
    fun address below => (memoryPost address below).trans (memory address below)⟩

#print axioms source_decode_header_extra_pointer_store
#print axioms source_decode_header_extra_length_store
#print axioms decode_header_extra_stores_reaches
end InitECandidate.Runtime
