import InitECandidate.Runtime.PayloadStoreTailReturnedEntries
import InitECandidate.Runtime.PayloadWithdrawalsReturned
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- The actual fixed-list count and final stores expose both hash slice
entries, without assuming a successful store or an independent count oracle. -/
theorem payload_withdrawals_returned_entries {F : Type} (state post : PanSemStateFiniteExact 64 F)
    (payload input length wd balance : BitVec 64) (value : ValueHOL 64)
    (atPayload : state.locals.lookup (ofString "pl") = some (.val (.word payload)))
    (atInput : state.locals.lookup (ofString "p") = some (.val (.word input)))
    (atLength : state.locals.lookup (ofString "len") = some (.val (.word length)))
    (atWd : state.locals.lookup (ofString "o_wd") = some (.val (.word wd)))
    (atBalance : state.locals.lookup (ofString "o_bal") = some (.val (.word balance)))
    (code : state.code = originalRuntimeCode)
    (run : evaluateHOLFiniteState state (payloadAt 19) = (some (.returned value),post)) :
    (balance - wd) % 44 = 0 ∧ ((balance - wd) / 44).toNat < 2^63 ∧
      RlpSliceEntry post payload 3 (input + wd) ((balance - wd) / 44) ∧
      RlpSliceEntry post payload 4 (input + balance) (length - balance) := by
  obtain ⟨divisible,within,bodyPost,output,tail,memory,_,domain⟩ :=
    payload_withdrawals_suffix_returned state post wd balance value atWd atBalance code run
  let entry := setVarHOLFinite (ofString "nwd") (.val (.word ((balance - wd) / 44)))
    {bodyPost with locals := state.locals}
  have keep (key : MlS) (different : key ≠ ofString "nwd") : entry.locals.lookup key = state.locals.lookup key := by
    simp [entry,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,Ne.symm different]
  have count : entry.locals.lookup (ofString "nwd") = some (.val (.word ((balance - wd) / 44))) := by
    simp [entry,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]
  have entries := payload_store_tail_returned_entries entry output payload input length wd balance ((balance - wd) / 44) value
    ((keep _ (by decide)).trans atPayload) ((keep _ (by decide)).trans atInput) ((keep _ (by decide)).trans atLength)
    ((keep _ (by decide)).trans atWd) ((keep _ (by decide)).trans atBalance) count tail
  exact ⟨divisible,within,
    entries.1.after_frame output post payload 3 _ _ domain (congrFun memory _) (congrFun memory _),
    entries.2.after_frame output post payload 4 _ _ domain (congrFun memory _) (congrFun memory _)⟩

/-- Ordered offsets inside the bounded input give the finite hash-loop count
and request-byte limits used by the payload runtime contract. -/
theorem payload_tail_hash_bounds (length wd balance : BitVec 64)
    (small : length.toNat ≤ 134217712) (ordered : wd.toNat ≤ balance.toNat)
    (inside : balance.toNat ≤ length.toNat) :
    ((balance - wd) / 44).toNat ≤ 134217712 ∧ (length - balance).toNat ≤ 134217712 := by
  have wdSub : (balance - wd).toNat = balance.toNat - wd.toNat := BitVec.toNat_sub_of_le ordered
  have requestSub : (length - balance).toNat = length.toNat - balance.toNat := BitVec.toNat_sub_of_le inside
  rw [BitVec.toNat_udiv,wdSub,requestSub]
  change (balance.toNat - wd.toNat) / 44 ≤ 134217712 ∧ length.toNat - balance.toNat ≤ 134217712
  omega

#print axioms payload_withdrawals_returned_entries
#print axioms payload_tail_hash_bounds
end InitECandidate.Runtime
