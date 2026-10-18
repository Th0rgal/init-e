import InitECandidate.Runtime.HtabFindSlotBound
import InitECandidate.Runtime.MemcpyCallBound
import InitECandidate.Runtime.OriginalHashInsertCode
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
open InitECandidate.Proofs.FrontendCodecComputation

def htabInsertRawDecoded : ProgHOL 64 :=
  match declToHOLStructural Guest.guestFn_htab_insert_raw with | .function fn => fn.body | _ => .skip

def htabInsertRawFinish : ProgHOL 64 :=
  match htabInsertRawDecoded with
  | .dec _ _ _ (.dec _ _ _ (.dec _ _ _ (.dec _ _ _ (.dec _ _ _ (.dec _ _ _ (.dec _ _ _
      (.decCall _ _ _ _ (.dec _ _ _ (.seq _ (.seq _ rest)))))))))) => rest
  | _ => .skip

theorem source_htabInsertRaw_body : sourceFunctionBody Guest.guestFn_htab_insert_raw =
    .dec (ofString "cap") .one (.load .one (hashLocalAddress (ofString "t") 16))
      (.dec (ofString "klen") .one (.load .one (hashLocalAddress (ofString "t") 0))
        (.dec (ofString "stride") .one (.load .one (hashLocalAddress (ofString "t") 8))
          (.dec (ofString "keys") .one (.load .one (hashLocalAddress (ofString "t") 32))
            (.dec (ofString "used") .one (.load .one (hashLocalAddress (ofString "t") 48))
              (.dec (ofString "order") .one (.load .one (hashLocalAddress (ofString "t") 56))
                (.dec (ofString "order_pos") .one (.load .one (hashLocalAddress (ofString "t") 64))
                  (.decCall (ofString "h") .one (ofString "htab_hash")
                      [.var .local (ofString "key"),.var .local (ofString "klen")]
                    (.dec (ofString "i") .one hashFindIndexExpression
                      (.seq (.while (hashProbeOccupied (ofString "i")) (hashProbeStep (ofString "i")))
                        (.seq (.call (some (none,none)) (ofString "memcpy")
                            [hashFindComparisonAddress,.var .local (ofString "key"),.var .local (ofString "klen")])
                          htabInsertRawFinish)))))))))) := by
  unfold sourceFunctionBody
  rw [declToHOL_eq]
  rfl

theorem htabInsertRaw_finish_straight : extStraightLine htabInsertRawFinish = true := by decide

/-- The actual insertion probe loop, from rank n, spends at most n ticks in
every outcome: it advances cyclically toward the known empty slot; unreadable
occupancy bytes end the run. -/
theorem hashInsertLoop_run (capacity used empty keyLength : BitVec 64) (bits : Nat)
    (power : capacity.toNat = 2 ^ bits) (emptyInside : empty.toNat < capacity.toNat) :
    ∀ n : Nat, ∀ {F : Type} (state : PanSemStateFiniteExact 64 F), state.code = originalRuntimeCode →
      FindProbeRank capacity used empty keyLength state n → n * (0 + 1) ≤ state.clock →
      RankedOutcome state (hashProbeOccupied (ofString "i")) (n * (0 + 1))
        (FindProbeRank capacity used empty keyLength) False
        (evaluateHOLFiniteState state (.while (hashProbeOccupied (ofString "i")) (hashProbeStep (ofString "i")))) := by
  refine rankedWhile_run (hashProbeOccupied (ofString "i")) (hashProbeStep (ofString "i")) 0
    (FindProbeRank capacity used empty keyLength) False ?_ ?_
  · intro F s ranked v hv
    obtain ⟨_,usedL,_,_,_,_,emptyB,index,iL,inside,dist⟩ := ranked
    have same : index = empty := by
      apply BitVec.eq_of_toNat_eq
      unfold hashProbeDistance at dist
      split at dist <;> omega
    subst same
    rw [evalHOLFinite_eq_toExact,eval_hashProbeOccupied s _ index used 0 iL usedL emptyB] at hv
    simp [Compiler.Encoders.Asm.wordCmpHOL] at hv
    exact hv.symm
  · intro F s n v code' ranked hv nonzero budget'
    obtain ⟨capL,usedL,lenL,keysE,strideE,keyE,emptyB,index,iL,inside,dist⟩ := ranked
    have differs : index.toNat ≠ empty.toNat := by
      intro same
      have equal : index = empty := BitVec.eq_of_toNat_eq same
      subst equal
      rw [evalHOLFinite_eq_toExact,eval_hashProbeOccupied s _ index used 0 iL usedL emptyB] at hv
      simp [Compiler.Encoders.Asm.wordCmpHOL] at hv
      exact nonzero hv.symm
    rw [evaluate_hashProbeStep (decClockHOLFinite s) (ofString "i") index capacity iL capL]
    have keep : ∀ k, k ≠ ofString "i" →
        (setVarHOLFinite (ofString "i") (.val (.word (hashProbeNext index capacity))) (decClockHOLFinite s)).locals.lookup k =
          s.locals.lookup k := by
      intro k ne
      simp [setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,Ne.symm ne]
      rfl
    have wrap := hashProbeNext_wrap index capacity bits power inside
    have nextInside : (hashProbeNext index capacity).toNat < capacity.toNat := by
      rw [hashProbeNext_toNat index capacity bits power inside]
      exact Nat.mod_lt _ (by rw [power]; exact Nat.two_pow_pos bits)
    have decreased := hashProbeDistance_decreases capacity.toNat index.toNat empty.toNat inside emptyInside differs
    rw [← wrap] at decreased
    obtain ⟨keys,keysL⟩ := keysE
    obtain ⟨stride,strideL⟩ := strideE
    obtain ⟨key,keyL⟩ := keyE
    refine ⟨by simp [setVarHOLFinite,decClockHOLFinite],by simp [setVarHOLFinite,decClockHOLFinite],by simp,?_,
      by intro h; simp at h⟩
    intro _
    refine ⟨n,le_refl _,⟨?_,?_,?_,⟨keys,?_⟩,⟨stride,?_⟩,⟨key,?_⟩,emptyB,hashProbeNext index capacity,?_,nextInside,
      by omega⟩,rfl⟩
    · rw [keep _ (by decide)]; exact capL
    · rw [keep _ (by decide)]; exact usedL
    · rw [keep _ (by decide)]; exact lenL
    · rw [keep _ (by decide)]; exact keysL
    · rw [keep _ (by decide)]; exact strideL
    · rw [keep _ (by decide)]; exact keyL
    · simp [setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]

#print axioms hashInsertLoop_run

/-- `htab_insert_raw` from a state with the same readable-header and empty-slot
premises as lookup spends at most
klen / 8 + 9 + cap + klen / 32 + klen / 8 + 11 ticks in every outcome. The
order arrays, value array and key bytes need not be readable. -/
theorem evaluate_htabInsertRaw_body_bounded {F : Type} (state : PanSemStateFiniteExact 64 F)
    (code : state.code = originalRuntimeCode)
    (table key capacity keyLength stride keys used empty : BitVec 64) (bits : Nat)
    (tableLocal : state.locals.lookup (ofString "t") = some (.val (.word table)))
    (keyLocal : state.locals.lookup (ofString "key") = some (.val (.word key)))
    (domain16 : state.memaddrs (table + 16)) (cell16 : state.memory (table + 16) = .word capacity)
    (domain0 : state.memaddrs (table + 0)) (cell0 : state.memory (table + 0) = .word keyLength)
    (domain8 : state.memaddrs (table + 8)) (cell8 : state.memory (table + 8) = .word stride)
    (domain32 : state.memaddrs (table + 32)) (cell32 : state.memory (table + 32) = .word keys)
    (domain48 : state.memaddrs (table + 48)) (cell48 : state.memory (table + 48) = .word used)
    (power : capacity.toNat = 2 ^ bits) (emptyInside : empty.toNat < capacity.toNat)
    (emptyByte : @panMemLoadByteHOL 64 _ state.memory state.memaddrs
      (fun a => Classical.propDecidable (state.memaddrs a)) state.be (used + empty) = some 0)
    (small : keyLength.toNat ≤ 33806089496)
    (budget : keyLength.toNat / 8 + 8 + 1 +
      (capacity.toNat * (0 + 1) + (keyLength.toNat / 32 + keyLength.toNat / 8 + 11 + 0)) ≤ state.clock) :
    RunBounded state (sourceFunctionBody Guest.guestFn_htab_insert_raw)
      (keyLength.toNat / 8 + 8 + 1 +
        (capacity.toNat * (0 + 1) + (keyLength.toNat / 32 + keyLength.toNat / 8 + 11 + 0))) := by
  have names : ofString "cap" ≠ ofString "t" ∧ ofString "klen" ≠ ofString "t" ∧ ofString "stride" ≠ ofString "t" ∧
      ofString "keys" ≠ ofString "t" := by decide
  rw [source_htabInsertRaw_body]
  apply runBounded_header_load _ _ _ table 16 capacity _ tableLocal domain16 cell16
  apply runBounded_header_load _ _ _ table 0 keyLength _
    (by simp [setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,names.1,tableLocal]) (by exact domain0) (by exact cell0)
  apply runBounded_header_load _ _ _ table 8 stride _
    (by simp [setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,names.1,names.2.1,tableLocal])
    (by exact domain8) (by exact cell8)
  apply runBounded_header_load _ _ _ table 32 keys _
    (by simp [setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,names.1,names.2.1,names.2.2.1,tableLocal])
    (by exact domain32) (by exact cell32)
  apply runBounded_header_load _ _ _ table 48 used _
    (by simp [setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,names.1,names.2.1,names.2.2.1,names.2.2.2,
      tableLocal]) (by exact domain48) (by exact cell48)
  generalize hloaded : setVarHOLFinite (ofString "used") (.val (.word used)) (setVarHOLFinite (ofString "keys") (.val (.word keys))
    (setVarHOLFinite (ofString "stride") (.val (.word stride)) (setVarHOLFinite (ofString "klen") (.val (.word keyLength))
      (setVarHOLFinite (ofString "cap") (.val (.word capacity)) state)))) = loaded
  have lookups : loaded.locals.lookup (ofString "cap") = some (.val (.word capacity)) ∧
      loaded.locals.lookup (ofString "klen") = some (.val (.word keyLength)) ∧
      loaded.locals.lookup (ofString "stride") = some (.val (.word stride)) ∧
      loaded.locals.lookup (ofString "keys") = some (.val (.word keys)) ∧
      loaded.locals.lookup (ofString "used") = some (.val (.word used)) ∧
      loaded.locals.lookup (ofString "key") = some (.val (.word key)) := by
    rw [← hloaded]
    refine ⟨?_,?_,?_,?_,?_,?_⟩ <;>
      simp [setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,keyLocal,
        show ofString "used" ≠ ofString "cap" by decide,show ofString "keys" ≠ ofString "cap" by decide,
        show ofString "stride" ≠ ofString "cap" by decide,show ofString "klen" ≠ ofString "cap" by decide,
        show ofString "used" ≠ ofString "klen" by decide,show ofString "keys" ≠ ofString "klen" by decide,
        show ofString "stride" ≠ ofString "klen" by decide,show ofString "used" ≠ ofString "stride" by decide,
        show ofString "keys" ≠ ofString "stride" by decide,show ofString "used" ≠ ofString "keys" by decide,
        show ofString "used" ≠ ofString "key" by decide,show ofString "keys" ≠ ofString "key" by decide,
        show ofString "stride" ≠ ofString "key" by decide,show ofString "klen" ≠ ofString "key" by decide,
        show ofString "cap" ≠ ofString "key" by decide]
  have loadedFacts : loaded.code = originalRuntimeCode ∧ loaded.memory = state.memory ∧
      loaded.memaddrs = state.memaddrs ∧ loaded.be = state.be ∧ loaded.clock = state.clock := by
    rw [← hloaded]; exact ⟨code,rfl,rfl,rfl,rfl⟩
  obtain ⟨capL,lenL,strideL,keysL,usedL,keyL⟩ := lookups
  -- order and order_pos: any loaded values
  apply RunBounded.dec
  intro order _
  apply RunBounded.dec
  intro orderPos _
  generalize hordered : setVarHOLFinite (ofString "order_pos") orderPos (setVarHOLFinite (ofString "order") order loaded) = ordered
  have orderedLookup : ∀ k, k ≠ ofString "order_pos" → k ≠ ofString "order" →
      ordered.locals.lookup k = loaded.locals.lookup k := by
    intro k n1 n2
    rw [← hordered]
    simp [setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,Ne.symm n1,Ne.symm n2]
  have orderedFacts : ordered.code = originalRuntimeCode ∧ ordered.memory = state.memory ∧
      ordered.memaddrs = state.memaddrs ∧ ordered.be = state.be ∧ ordered.clock = state.clock := by
    rw [← hordered]; exact loadedFacts
  have args : evalListHOLFinite ordered (h := fun a => Classical.propDecidable (ordered.memaddrs a))
      [.var .local (ofString "key"),.var .local (ofString "klen")] =
        some [.val (.word key),.val (.word keyLength)] := by
    rw [evalListHOLFinite_eq_toExact]
    have keyO := (orderedLookup (ofString "key") (by decide) (by decide)).trans keyL
    have lenO := (orderedLookup (ofString "klen") (by decide) (by decide)).trans lenL
    simp [evalListHOLExact,evalHOLExact,keyO,lenO]
  apply runBounded_htabHash_decCall ordered _ _ _ _ key keyLength orderedFacts.1 args (by omega)
    (by rw [orderedFacts.2.2.2.2]; exact budget)
  intro value post pc pm pa pb _ tc
  apply RunBounded.dec
  intro index evaluated
  generalize hresumed : setVarHOLFinite (ofString "h") value {post with locals := ordered.locals} = resumed at evaluated ⊢
  have resumedLookup : ∀ k, k ≠ ofString "h" → k ≠ ofString "order_pos" → k ≠ ofString "order" →
      resumed.locals.lookup k = loaded.locals.lookup k := by
    intro k nh n1 n2
    rw [← hresumed]
    simp [setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,Ne.symm nh]
    exact orderedLookup k n1 n2
  have valueL : resumed.locals.lookup (ofString "h") = some value := by
    rw [← hresumed]; simp [setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]
  have capR : resumed.locals.lookup (ofString "cap") = some (.val (.word capacity)) := by
    rw [resumedLookup _ (by decide) (by decide) (by decide)]; exact capL
  cases value with
  | val word =>
    cases word with
    | word hash =>
      rw [eval_hashFind_initial_index resumed hash capacity valueL capR] at evaluated
      cases evaluated
      generalize hentry : setVarHOLFinite (ofString "i") (.val (.word (hashFindInitialIndex hash capacity))) resumed = entry
      have entryLookup : ∀ k, k ≠ ofString "i" → k ≠ ofString "h" → k ≠ ofString "order_pos" → k ≠ ofString "order" →
          entry.locals.lookup k = loaded.locals.lookup k := by
        intro k ni nh n1 n2
        rw [← hentry]
        simp [setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,Ne.symm ni]
        exact resumedLookup k nh n1 n2
      have entryFacts : entry.code = originalRuntimeCode ∧ entry.memory = state.memory ∧ entry.memaddrs = state.memaddrs ∧
          entry.be = state.be ∧ entry.clock = post.clock := by
        rw [← hentry,← hresumed]
        exact ⟨pc.trans orderedFacts.1,pm.trans orderedFacts.2.1,pa.trans orderedFacts.2.2.1,
          pb.trans orderedFacts.2.2.2.1,rfl⟩
      have range := hashFind_initial_index_bound hash capacity bits power
      have ranked : FindProbeRank capacity used empty keyLength entry capacity.toNat := by
        refine ⟨?_,?_,?_,⟨keys,?_⟩,⟨stride,?_⟩,⟨key,?_⟩,?_,hashFindInitialIndex hash capacity,?_,range.2,?_⟩
        · rw [entryLookup _ (by decide) (by decide) (by decide) (by decide)]; exact capL
        · rw [entryLookup _ (by decide) (by decide) (by decide) (by decide)]; exact usedL
        · rw [entryLookup _ (by decide) (by decide) (by decide) (by decide)]; exact lenL
        · rw [entryLookup _ (by decide) (by decide) (by decide) (by decide)]; exact keysL
        · rw [entryLookup _ (by decide) (by decide) (by decide) (by decide)]; exact strideL
        · rw [entryLookup _ (by decide) (by decide) (by decide) (by decide)]; exact keyL
        · rw [entryFacts.2.1,entryFacts.2.2.1,entryFacts.2.2.2.1]; exact emptyByte
        · rw [← hentry]; simp [setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]
        · exact Nat.le_of_lt (hashProbeDistance_lt_capacity _ _ _ range.2 emptyInside)
      have loop := hashInsertLoop_run capacity used empty keyLength bits power emptyInside capacity.toNat entry
        entryFacts.1 ranked (by rw [entryFacts.2.2.2.2]; omega)
      refine RunBounded.seq ⟨loop.1,loop.2.1,loop.2.2.1⟩ (by rw [entryFacts.2.2.2.2]; omega) ?_
      intro probed probeRun probedCode probedBudget
      have exited := loop.2.2.2
      rw [probeRun] at exited
      obtain ⟨_,⟨_,_,lenP,⟨keys',keysP⟩,⟨stride',strideP⟩,⟨key',keyP⟩,_,index',indexP,_,_⟩,_,_⟩ := exited rfl
      obtain ⟨address,copyArgs⟩ := eval_hashFind_comparison_args probed index' keys' stride' key' keyLength
        indexP keysP strideP keyP lenP
      have copy := evaluate_memcpy_call_bounded probed _ address key' keyLength copyArgs
        (probedCode.trans entryFacts.1) small (by omega)
      refine RunBounded.seq ⟨copy.1,copy.2.1,copy.2.2⟩ (by omega) ?_
      intro final _ finalCode _
      exact RunBounded.ofProg (ProgBounded.straight _ htabInsertRaw_finish_straight)
        (finalCode.trans (probedCode.trans entryFacts.1)) (Nat.zero_le _)
  | _ =>
    simp [hashFindIndexExpression,evalHOLExact,evalListHOLExact,valueL,capR,valueIsWord,wordOpHOL,wordOp,valueWord] at evaluated

#print axioms evaluate_htabInsertRaw_body_bounded

/-- A handler-free `htab_insert_raw` call on word arguments, from a caller with
the lookup premises, costs one tick more than the body bound, in every outcome. -/
theorem runBounded_htabInsertRaw_call {F : Type} (state : PanSemStateFiniteExact 64 F)
    (destination : Option (VarKind × MlS)) (tableArgument keyArgument valueArgument : ExpHOL 64)
    (table key value capacity keyLength stride keys used empty : BitVec 64) (bits : Nat)
    (code : state.code = originalRuntimeCode)
    (args : evalListHOLFinite state (h := fun a => Classical.propDecidable (state.memaddrs a))
      [tableArgument,keyArgument,valueArgument] = some [.val (.word table),.val (.word key),.val (.word value)])
    (domain16 : state.memaddrs (table + 16)) (cell16 : state.memory (table + 16) = .word capacity)
    (domain0 : state.memaddrs (table + 0)) (cell0 : state.memory (table + 0) = .word keyLength)
    (domain8 : state.memaddrs (table + 8)) (cell8 : state.memory (table + 8) = .word stride)
    (domain32 : state.memaddrs (table + 32)) (cell32 : state.memory (table + 32) = .word keys)
    (domain48 : state.memaddrs (table + 48)) (cell48 : state.memory (table + 48) = .word used)
    (power : capacity.toNat = 2 ^ bits) (emptyInside : empty.toNat < capacity.toNat)
    (emptyByte : @panMemLoadByteHOL 64 _ state.memory state.memaddrs
      (fun a => Classical.propDecidable (state.memaddrs a)) state.be (used + empty) = some 0)
    (small : keyLength.toNat ≤ 33806089496)
    (budget : keyLength.toNat / 8 + 8 + 1 +
      (capacity.toNat * (0 + 1) + (keyLength.toNat / 32 + keyLength.toNat / 8 + 11 + 0)) + 1 ≤ state.clock) :
    RunBounded state (.call (some (destination,none)) (ofString "htab_insert_raw") [tableArgument,keyArgument,valueArgument])
      (keyLength.toNat / 8 + 8 + 1 +
        (capacity.toNat * (0 + 1) + (keyLength.toNat / 32 + keyLength.toNat / 8 + 11 + 0)) + 1) := by
  refine RunBounded.call args budget ?_
  intro body locals returnShape lookup
  have installed : state.code.lookup (ofString "htab_insert_raw") =
      some ([(ofString "t",.one),(ofString "key",.one),(ofString "value",.one)],
        sourceFunctionBody Guest.guestFn_htab_insert_raw,.one) := by
    rw [code]; exact originalRuntimeCode_hashInsert_lookup
  rw [pan_three_word_lookup state.code.lookup (ofString "htab_insert_raw") (ofString "t") (ofString "key")
    (ofString "value") (sourceFunctionBody Guest.guestFn_htab_insert_raw) table key value
    (by decide) (by decide) (by decide) installed] at lookup
  cases lookup
  refine evaluate_htabInsertRaw_body_bounded _ (by exact code) table key capacity keyLength stride keys used empty bits
    ?_ ?_ (by exact domain16) (by exact cell16) (by exact domain0) (by exact cell0) (by exact domain8) (by exact cell8)
    (by exact domain32) (by exact cell32) (by exact domain48) (by exact cell48) power emptyInside
    (by exact emptyByte) small ?_
  · simp [callEntryStateHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,
      show ofString "key" ≠ ofString "t" by decide,show ofString "value" ≠ ofString "t" by decide]
  · simp [callEntryStateHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,show ofString "value" ≠ ofString "key" by decide]
  · change _ ≤ state.clock - 1; omega

#print axioms runBounded_htabInsertRaw_call
end InitECandidate.Runtime
