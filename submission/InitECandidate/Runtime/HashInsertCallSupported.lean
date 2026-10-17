import InitECandidate.Runtime.HashInsertBodySupported
import InitECandidate.Runtime.OriginalHashInsertCode
import InitECandidate.Runtime.PanThreeWordLookup
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- Actual insertion call, including argument binding and its entry clock. -/
theorem evaluate_hashInsert_supported_call {F : Type} (state : PanSemStateFiniteExact 64 F)
    (tableArgument keyArgument valueArgument : ExpHOL 64)
    (table keys stride key capacity used values value order orderPos count keyLength : BitVec 64) (bits : Nat)
    (supported : keyLength = 20 ∨ keyLength = 32 ∨ keyLength = 52)
    (code : state.code = originalRuntimeCode) (power : capacity.toNat = 2 ^ bits)
    (domain16 : state.memaddrs (table + 16)) (cell16 : state.memory (table + 16) = .word capacity)
    (domain0 : state.memaddrs (table + 0)) (cell0 : state.memory (table + 0) = .word keyLength)
    (domain8 : state.memaddrs (table + 8)) (cell8 : state.memory (table + 8) = .word stride)
    (domain32 : state.memaddrs (table + 32)) (cell32 : state.memory (table + 32) = .word keys)
    (domain48 : state.memaddrs (table + 48)) (cell48 : state.memory (table + 48) = .word used)
    (domain56 : state.memaddrs (table + 56)) (cell56 : state.memory (table + 56) = .word order)
    (domain64 : state.memaddrs (table + 64)) (cell64 : state.memory (table + 64) = .word orderPos)
    (facts : HashInsertTableMemory capacity used table values order orderPos count state)
    (keysAligned : keys.toNat % 8 = 0) (strideAligned : stride.toNat % 8 = 0)
    (keyAligned : key.toNat % 8 = 0) (usedAligned : used.toNat % 8 = 0)
    (headerBefore : table.toNat + 72 ≤ keys.toNat)
    (keysBefore : keys.toNat + capacity.toNat * stride.toNat ≤ used.toNat)
    (usedBound : used.toNat + capacity.toNat ≤ 33806089496) (fits : keyLength.toNat ≤ stride.toNat)
    (arrayDomain : ∀ address : BitVec 64, keys.toNat ≤ address.toNat →
      address.toNat < keys.toNat + capacity.toNat * stride.toNat → state.memaddrs address)
    (sourceWordDomain : ∀ offset : Nat, offset < keyLength.toNat → state.memaddrs (key + BitVec.ofNat 64 offset))
    (sourceByteDomain : ∀ offset : Nat, offset < keyLength.toNat → state.memaddrs (panByteAlignHOL (key + BitVec.ofNat 64 offset)))
    (readable : ∀ current : BitVec 64, current.toNat < capacity.toNat → ∃ byte, hashOccupancyRead state used current = some byte)
    (room : hashOccupiedCount capacity (hashOccupancyRead state used) < capacity.toNat)
    (budget : capacity.toNat + keyLength.toNat + 3 ≤ state.clock)
    (arguments : evalListHOLFinite state
      (h := fun address => Classical.propDecidable (state.memaddrs address))
      [tableArgument,keyArgument,valueArgument] = some [.val (.word table),.val (.word key),.val (.word value)]) :
    ∃ post, evaluateHOLFiniteState state (.call (some (none,none)) (ofString "htab_insert_raw")
        [tableArgument,keyArgument,valueArgument]) = (none,post) ∧
      post.memory (table + 24) = .word (count + 1) ∧
      (count + 1).toNat = hashOccupiedCount capacity (hashOccupancyRead post used) ∧
      state.clock ≤ post.clock + capacity.toNat + keyLength.toNat + 3 ∧ post.clock ≤ state.clock ∧ post.locals = state.locals := by
  let callee : HolFiniteMapExact MlS (ValueHOL 64) :=
    ((HolFiniteMapExact.empty.update (ofString "t",.val (.word table))).update
      (ofString "key",.val (.word key))).update (ofString "value",.val (.word value))
  let entry := callEntryStateHOLFinite state callee
  have vt : ofString "value" ≠ ofString "t" := by decide
  have vk : ofString "value" ≠ ofString "key" := by decide
  have kt : ofString "key" ≠ ofString "t" := by decide
  have t : entry.locals.lookup (ofString "t") = some (.val (.word table)) := by
    simp [entry,callEntryStateHOLFinite,callee,HolFiniteMapExact.lookup_update,FUPDATE,vt,kt]
  have k : entry.locals.lookup (ofString "key") = some (.val (.word key)) := by
    simp [entry,callEntryStateHOLFinite,callee,HolFiniteMapExact.lookup_update,FUPDATE,vk]
  have v : entry.locals.lookup (ofString "value") = some (.val (.word value)) := by
    simp [entry,callEntryStateHOLFinite,callee,HolFiniteMapExact.lookup_update,FUPDATE]
  have entryFacts : HashInsertTableMemory capacity used table values order orderPos count entry := by
    rcases facts with ⟨a,b,c,d,e,f,g,h,i,j,k,l,m⟩
    exact ⟨a,b,c,d,e,f,g,h,i,j,k,l,m⟩
  obtain ⟨post,body,header,agreement,cost,remaining⟩ := evaluate_source_hashInsert_supported entry
    table keys stride key capacity used values value order orderPos count keyLength bits supported code power t k v
    domain16 cell16 domain0 cell0 domain8 cell8 domain32 cell32 domain48 cell48 domain56 cell56 domain64 cell64
    entryFacts keysAligned strideAligned keyAligned usedAligned headerBefore keysBefore usedBound fits
    arrayDomain sourceWordDomain sourceByteDomain readable room
    (by change capacity.toNat + keyLength.toNat + 2 ≤ state.clock - 1; omega)
  have installed : state.code.lookup (ofString "htab_insert_raw") =
      some ([(ofString "t",.one),(ofString "key",.one),(ofString "value",.one)],sourceFunctionBody Guest.guestFn_htab_insert_raw,.one) := by
    rw [code]; exact originalRuntimeCode_hashInsert_lookup
  have lookup := pan_three_word_lookup state.code.lookup (ofString "htab_insert_raw")
    (ofString "t") (ofString "key") (ofString "value") (sourceFunctionBody Guest.guestFn_htab_insert_raw)
    table key value (by decide) (by decide) (by decide) installed
  have call := evaluateHOLFiniteState_call_return_caller_locals state none (ofString "htab_insert_raw")
    [tableArgument,keyArgument,valueArgument] [.val (.word table),.val (.word key),.val (.word value)]
    (sourceFunctionBody Guest.guestFn_htab_insert_raw) callee .one (.val (.word 0)) post arguments lookup (by omega) body
    (by simp [shapeOfHOLExact,shapeEqHOL])
  refine ⟨{post with locals := state.locals},call,header,agreement,?_,?_,rfl⟩
  · change state.clock ≤ post.clock + capacity.toNat + keyLength.toNat + 3
    change state.clock - 1 ≤ post.clock + capacity.toNat + keyLength.toNat + 2 at cost
    omega
  · change post.clock ≤ state.clock
    change post.clock ≤ state.clock - 1 at remaining
    omega

#print axioms evaluate_hashInsert_supported_call
end InitECandidate.Runtime
