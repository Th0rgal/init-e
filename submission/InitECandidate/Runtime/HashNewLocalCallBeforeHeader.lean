import InitECandidate.Runtime.HashNewCallBeforeHeader
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- Assigning the constructor result also preserves every earlier allocation. -/
theorem evaluate_htabNew_local_call_before_header {F : Type} (state : PanSemStateFiniteExact 64 F)
    (keyArgument capacityArgument : ExpHOL 64) (table keyLength capacity : BitVec 64)
    (arguments : evalListHOLFinite state
      (h := fun address => Classical.propDecidable (state.memaddrs address)) [keyArgument,capacityArgument] =
        some [.val (.word keyLength),.val (.word capacity)])
    (code : state.code = originalRuntimeCode) (ticks : capacity.toNat + 8 ≤ state.clock)
    (heap : state.globals.lookup (ofString "heap_ptr") = some (.val (.word table)))
    (keyBound : keyLength.toNat ≤ 52) (tableAligned : table.toNat % 8 = 0)
    (budget : table.toNat + 81 * capacity.toNat + 114 ≤ 33806089496)
    (headerDomain : ∀ offset : Nat, offset ≤ 64 → state.memaddrs (table + BitVec.ofNat 64 offset))
    (wordDomain : ∀ offset : Nat, offset < capacity.toNat →
      state.memaddrs (htabNewUsed table keyLength capacity + BitVec.ofNat 64 offset))
    (byteDomain : ∀ offset : Nat, offset < capacity.toNat →
      state.memaddrs (panByteAlignHOL (htabNewUsed table keyLength capacity + BitVec.ofNat 64 offset)))
    (name : MlS) (oldValue : BitVec 64)
    (localWord : state.locals.lookup name = some (.val (.word oldValue))) :
    ∃ post, evaluateHOLFiniteState state
        (.call (some (some (.local,name),none)) (ofString "htab_new") [keyArgument,capacityArgument]) = (none,post) ∧
      state.clock ≤ post.clock + capacity.toNat + 8 ∧ post.clock ≤ state.clock ∧
      ∀ address : BitVec 64, address.toNat < table.toNat → post.memory address = state.memory address := by
  let callee : HolFiniteMapExact MlS (ValueHOL 64) :=
    (HolFiniteMapExact.empty.update (ofString "key_len",.val (.word keyLength))).update (ofString "cap",.val (.word capacity))
  let entry := callEntryStateHOLFinite state callee
  have different : ofString "cap" ≠ ofString "key_len" := by decide
  have keyLocal : entry.locals.lookup (ofString "key_len") = some (.val (.word keyLength)) := by
    simp [entry,callEntryStateHOLFinite,callee,HolFiniteMapExact.lookup_update,FUPDATE,different]
  have capLocal : entry.locals.lookup (ofString "cap") = some (.val (.word capacity)) := by
    simp [entry,callEntryStateHOLFinite,callee,HolFiniteMapExact.lookup_update,FUPDATE]
  obtain ⟨post,body,_,cost,remaining,_,_,_,memoryFrame⟩ :=
    evaluate_source_htabNew_before_header entry table keyLength capacity code (by change capacity.toNat + 7 ≤ state.clock - 1; omega)
      heap keyBound tableAligned budget keyLocal capLocal headerDomain wordDomain byteDomain
  have installed : state.code.lookup (ofString "htab_new") =
      some ([(ofString "key_len",.one),(ofString "cap",.one)],sourceFunctionBody Guest.guestFn_htab_new,.one) := by
    rw [code]; exact originalRuntimeCode_htabNew_lookup
  have lookup := pan_two_word_lookup state.code.lookup (ofString "htab_new") (ofString "key_len") (ofString "cap")
    (sourceFunctionBody Guest.guestFn_htab_new) keyLength capacity (by decide) installed
  have shapeOk : shapeEqHOL (shapeOfHOLExact (.val (.word table))) .one = true := by
    simp [shapeEqHOL,shapeOfHOLExact]
  have valid : isValidValueHOLExact state.toExact .local name (.val (.word table)) = true := by
    simp [isValidValueHOLExact,lookupKvarHOLExact,localWord,shapeOfHOLExact,shapeEqHOL]
  have assigned := evaluateHOLFiniteState_call_return_set_kvar state .local name none (ofString "htab_new")
    [keyArgument,capacityArgument] [.val (.word keyLength),.val (.word capacity)]
    (sourceFunctionBody Guest.guestFn_htab_new) callee .one (.val (.word table)) post arguments lookup (by omega) body shapeOk valid
  refine ⟨_,assigned,?_,?_,memoryFrame⟩
  · change state.clock ≤ post.clock + capacity.toNat + 8
    change state.clock - 1 ≤ post.clock + capacity.toNat + 7 at cost
    omega
  · change post.clock ≤ state.clock
    change post.clock ≤ state.clock - 1 at remaining
    omega

#print axioms evaluate_htabNew_local_call_before_header
end InitECandidate.Runtime
