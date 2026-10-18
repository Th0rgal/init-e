import InitECandidate.Runtime.HtabHashBound
import InitECandidate.Runtime.MemeqBody64BoundCap
import InitECandidate.Runtime.MemeqReadFrame
import InitECandidate.Runtime.OriginalMemeqCode
import InitECandidate.Runtime.PanThreeWordLookup
import InitECandidate.Runtime.HashFindIteration32
import InitECandidate.Runtime.HashProbeLoop
import InitECandidate.Runtime.HashFindHashScope32
import InitECandidate.Runtime.HeaderLoadScope
import InitECandidate.Runtime.OriginalHashFindCode
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- A declared memeq call whose arguments are words, with any length up to the
heap cap, costs 4n + 1 plus its continuation, in every outcome; the
continuation runs with the caller's code, memory, addresses, endianness and
globals. -/
theorem runBounded_memeq_decCall {F : Type} (state : PanSemStateFiniteExact 64 F) (name : MlS)
    (leftArgument rightArgument sizeArgument : ExpHOL 64) (continuation : ProgHOL 64) (left right size : BitVec 64)
    (code : state.code = originalRuntimeCode)
    (args : evalListHOLFinite state (h := fun a => Classical.propDecidable (state.memaddrs a))
      [leftArgument,rightArgument,sizeArgument] = some [.val (.word left),.val (.word right),.val (.word size)])
    (small : size.toNat ≤ 33806089496) {tailCost : Nat}
    (budget : 4 * size.toNat + 1 + tailCost ≤ state.clock)
    (tail : ∀ value (post : PanSemStateFiniteExact 64 F), post.code = state.code → post.memory = state.memory →
      post.memaddrs = state.memaddrs → post.be = state.be → post.globals = state.globals → tailCost ≤ post.clock →
      RunBounded (setVarHOLFinite name value {post with locals := state.locals}) continuation tailCost) :
    RunBounded state (.decCall name .one (ofString "memeq") [leftArgument,rightArgument,sizeArgument] continuation)
      (4 * size.toNat + 1 + tailCost) := by
  refine RunBounded.decCall args budget ?_
  intro body locals returnShape lookup
  have installed : state.code.lookup (ofString "memeq") =
      some ([(ofString "a",.one),(ofString "b",.one),(ofString "n",.one)],sourceFunctionBody Guest.guestFn_memeq,.one) := by
    rw [code]; exact originalRuntimeCode_memeq_lookup
  rw [pan_three_word_lookup state.code.lookup (ofString "memeq") (ofString "a") (ofString "b") (ofString "n")
    (sourceFunctionBody Guest.guestFn_memeq) left right size (by decide) (by decide) (by decide) installed] at lookup
  cases lookup
  generalize hentry : callEntryStateHOLFinite state
    (((HolFiniteMapExact.empty.update (ofString "a",.val (.word left))).update (ofString "b",.val (.word right))).update
      (ofString "n",.val (.word size))) = entry
  have localN : entry.locals.lookup (ofString "n") = some (.val (.word size)) := by
    rw [← hentry]; simp [callEntryStateHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]
  have entryClock : entry.clock = state.clock - 1 := by rw [← hentry]; rfl
  have entryFacts : entry.code = state.code ∧ entry.memory = state.memory ∧ entry.memaddrs = state.memaddrs ∧
      entry.be = state.be ∧ entry.globals = state.globals := by
    rw [← hentry]; exact ⟨rfl,rfl,rfl,rfl,rfl⟩
  constructor
  · obtain ⟨result,post,run,spent,kept,safe⟩ := evaluate_memeq_body64_bounded_cap entry size localN small
      (by rw [entryClock]; omega)
    unfold RunBounded
    rw [run]
    exact ⟨spent,kept,safe⟩
  · intro value post run tc
    have meta' := evaluateHOLFiniteState_metadata entry (sourceFunctionBody Guest.guestFn_memeq)
    have memory := evaluate_readOnly_memory _ memeq_readOnlyMemory entry
    have globals := evaluate_readOnly_globals _ memeq_readOnlyMemory entry
    rw [run] at meta' memory globals
    exact tail value post (meta'.1.trans entryFacts.1) (memory.trans entryFacts.2.1) (meta'.2.1.trans entryFacts.2.2.1)
      (meta'.2.2.1.trans entryFacts.2.2.2.1) (globals.trans entryFacts.2.2.2.2) tc

#print axioms runBounded_memeq_decCall

/-- The only normal outcome of the lookup decision is a failed comparison
followed by the masked probe step. -/
theorem hashFindDecision_normal {F : Type} (state inner : PanSemStateFiniteExact 64 F) (index capacity : BitVec 64)
    (indexLocal : state.locals.lookup (ofString "i") = some (.val (.word index)))
    (capacityLocal : state.locals.lookup (ofString "cap") = some (.val (.word capacity)))
    (run : evaluateHOLFiniteState state hashFindDecision = (none,inner)) :
    inner.locals.lookup (ofString "i") = some (.val (.word (hashProbeNext index capacity))) := by
  cases equalLocal : state.locals.lookup (ofString "eq") with
  | none =>
    unfold hashFindDecision at run
    rw [evaluateHOLFiniteState_seq_line780,evaluateHOLFiniteState_ite] at run
    simp [evalHOLExact,equalLocal] at run
  | some value =>
    cases value with
    | val word =>
      cases word with
      | word equal =>
        by_cases zero : equal = 0
        · subst zero
          rw [evaluate_hashFind_mismatch state index capacity indexLocal capacityLocal equalLocal] at run
          cases run
          simp [setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]
        · rw [evaluate_hashFind_match state index equal zero indexLocal equalLocal] at run
          cases run
    | _ =>
      unfold hashFindDecision at run
      rw [evaluateHOLFiniteState_seq_line780,evaluateHOLFiniteState_ite] at run
      simp [evalHOLExact,equalLocal] at run

#print axioms hashFindDecision_normal

theorem hashFindIteration_probe {F : Type} (state post : PanSemStateFiniteExact 64 F) (index capacity : BitVec 64)
    (indexLocal : state.locals.lookup (ofString "i") = some (.val (.word index)))
    (capacityLocal : state.locals.lookup (ofString "cap") = some (.val (.word capacity)))
    (run : evaluateHOLFiniteState state hashFindIteration = (none,post)) :
    post.locals.lookup (ofString "i") = some (.val (.word (hashProbeNext index capacity))) := by
  unfold hashFindIteration at run
  obtain ⟨_,resumed,inner,agree,_,contRun,postLocals⟩ := decCall_flowing (Or.inl rfl) run
  have ie : ofString "i" ≠ ofString "eq" := by decide
  have ce : ofString "cap" ≠ ofString "eq" := by decide
  have innerIndex := hashFindDecision_normal resumed inner index capacity
    (by rw [agree _ ie]; exact indexLocal) (by rw [agree _ ce]; exact capacityLocal) contRun
  rw [postLocals,resVarEq_lookup,if_neg ie]
  exact innerIndex

theorem eval_hashFind_comparison_args {F : Type} (state : PanSemStateFiniteExact 64 F)
    (index keys stride key keyLength : BitVec 64)
    (indexLocal : state.locals.lookup (ofString "i") = some (.val (.word index)))
    (keysLocal : state.locals.lookup (ofString "keys") = some (.val (.word keys)))
    (strideLocal : state.locals.lookup (ofString "stride") = some (.val (.word stride)))
    (keyLocal : state.locals.lookup (ofString "key") = some (.val (.word key)))
    (lengthLocal : state.locals.lookup (ofString "klen") = some (.val (.word keyLength))) :
    ∃ address : BitVec 64, evalListHOLFinite state (h := fun a => Classical.propDecidable (state.memaddrs a))
      [hashFindComparisonAddress,.var .local (ofString "key"),.var .local (ofString "klen")] =
        some [.val (.word address),.val (.word key),.val (.word keyLength)] := by
  rw [evalListHOLFinite_eq_toExact]
  simp [hashFindComparisonAddress,evalListHOLExact,evalHOLExact,indexLocal,keysLocal,strideLocal,keyLocal,
    lengthLocal,wordOpHOL,wordOp,valueIsWord,valueWord,panOpHOL]

#print axioms hashFindIteration_probe

/-- Lookup-probe rank: the table locals are words (capacity, occupancy array
and key length fixed), the occupancy byte of a known empty slot still reads 0,
and the current index is in range at cyclic distance at most `n` from it. -/
def FindProbeRank (capacity used empty keyLength : BitVec 64) {F : Type} (s : PanSemStateFiniteExact 64 F) (n : Nat) : Prop :=
  s.locals.lookup (ofString "cap") = some (.val (.word capacity)) ∧
  s.locals.lookup (ofString "used") = some (.val (.word used)) ∧
  s.locals.lookup (ofString "klen") = some (.val (.word keyLength)) ∧
  (∃ keys : BitVec 64, s.locals.lookup (ofString "keys") = some (.val (.word keys))) ∧
  (∃ stride : BitVec 64, s.locals.lookup (ofString "stride") = some (.val (.word stride))) ∧
  (∃ key : BitVec 64, s.locals.lookup (ofString "key") = some (.val (.word key))) ∧
  @panMemLoadByteHOL 64 _ s.memory s.memaddrs (fun a => Classical.propDecidable (s.memaddrs a)) s.be (used + empty) = some 0 ∧
  ∃ index : BitVec 64, s.locals.lookup (ofString "i") = some (.val (.word index)) ∧ index.toNat < capacity.toNat ∧
    hashProbeDistance capacity.toNat index.toNat empty.toNat ≤ n

theorem hashFindDecision_readOnly : readOnlyMemory hashFindDecision = true := by decide

/-- The actual lookup probe loop, from rank n, spends at most n * (4 klen + 2)
ticks in every outcome: occupied probes compare keys (bounded memeq) and
advance cyclically toward the known empty slot; unreadable occupancy bytes and
failed comparisons end the run. -/
theorem hashFindLoop_run (capacity used empty keyLength : BitVec 64) (bits : Nat)
    (power : capacity.toNat = 2 ^ bits) (emptyInside : empty.toNat < capacity.toNat)
    (small : keyLength.toNat ≤ 33806089496) :
    ∀ n : Nat, ∀ {F : Type} (state : PanSemStateFiniteExact 64 F), state.code = originalRuntimeCode →
      FindProbeRank capacity used empty keyLength state n → n * (4 * keyLength.toNat + 1 + 0 + 1) ≤ state.clock →
      RankedOutcome state (hashProbeOccupied (ofString "i")) (n * (4 * keyLength.toNat + 1 + 0 + 1))
        (FindProbeRank capacity used empty keyLength) False (evaluateHOLFiniteState state hashFindLoop) := by
  have ie : ofString "i" ≠ ofString "eq" := by decide
  refine rankedWhile_run (hashProbeOccupied (ofString "i")) hashFindIteration (4 * keyLength.toNat + 1 + 0)
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
    obtain ⟨capL,usedL,lenL,⟨keys,keysL⟩,⟨stride,strideL⟩,⟨key,keyL⟩,emptyB,index,iL,inside,dist⟩ := ranked
    have differs : index.toNat ≠ empty.toNat := by
      intro same
      have equal : index = empty := BitVec.eq_of_toNat_eq same
      subst equal
      rw [evalHOLFinite_eq_toExact,eval_hashProbeOccupied s _ index used 0 iL usedL emptyB] at hv
      simp [Compiler.Encoders.Asm.wordCmpHOL] at hv
      exact nonzero hv.symm
    obtain ⟨address,args⟩ := eval_hashFind_comparison_args (decClockHOLFinite s) index keys stride key keyLength
      iL keysL strideL keyL lenL
    have bounded : RunBounded (decClockHOLFinite s) hashFindIteration (4 * keyLength.toNat + 1 + 0) := by
      unfold hashFindIteration
      exact runBounded_memeq_decCall (decClockHOLFinite s) _ _ _ _ _ address key keyLength (by exact code') args small
        (by change _ ≤ s.clock - 1; omega)
        (fun value post pc _ _ _ _ _ => RunBounded.ofProg (ProgBounded.straight _ (by decide))
          (by change post.code = _; exact pc.trans (by exact code')) (Nat.zero_le _))
    obtain ⟨b1,b2,b3⟩ := bounded
    have installed : (decClockHOLFinite s).code.lookup (ofString "memeq") =
        some ([(ofString "a",.one),(ofString "b",.one),(ofString "n",.one)],sourceFunctionBody Guest.guestFn_memeq,.one) := by
      rw [show (decClockHOLFinite s).code = s.code from rfl,code']; exact originalRuntimeCode_memeq_lookup
    have lookup := pan_three_word_lookup (decClockHOLFinite s).code.lookup (ofString "memeq") (ofString "a") (ofString "b")
      (ofString "n") (sourceFunctionBody Guest.guestFn_memeq) address key keyLength (by decide) (by decide) (by decide) installed
    have memory := (evaluate_decCall_readOnly_frame (decClockHOLFinite s) (ofString "eq") (ofString "memeq") .one .one
      _ _ _ hashFindDecision _ args lookup memeq_readOnlyMemory hashFindDecision_readOnly).1
    have meta' := evaluateHOLFiniteState_metadata (decClockHOLFinite s) hashFindIteration
    unfold hashFindIteration at b1 b2 b3 meta' ⊢
    refine ⟨b1,b2,b3,?_,?_⟩
    · intro flow
      rcases flow with normal | cont
      · cases run : evaluateHOLFiniteState (decClockHOLFinite s) (.decCall (ofString "eq") .one (ofString "memeq")
            [hashFindComparisonAddress,.var .local (ofString "key"),.var .local (ofString "klen")] hashFindDecision) with
        | mk result post =>
          rw [run] at normal memory meta'
          dsimp only at normal memory meta' ⊢
          subst normal
          have frame : ∀ k, avoidsLocal k hashFindIteration = true →
              post.locals.lookup k = s.locals.lookup k := by
            intro k avoid
            have kept := evaluate_avoidsLocal_flowing k hashFindIteration avoid (decClockHOLFinite s)
              (by unfold hashFindIteration; rw [run]; exact Or.inl rfl)
            unfold hashFindIteration at kept
            rw [run] at kept
            exact kept
          have nextIndex := hashFindIteration_probe (decClockHOLFinite s) post index capacity iL capL
            (by unfold hashFindIteration; exact run)
          have wrap := hashProbeNext_wrap index capacity bits power inside
          have nextInside : (hashProbeNext index capacity).toNat < capacity.toNat := by
            rw [hashProbeNext_toNat index capacity bits power inside]
            exact Nat.mod_lt _ (by rw [power]; exact Nat.two_pow_pos bits)
          have decreased := hashProbeDistance_decreases capacity.toNat index.toNat empty.toNat inside emptyInside differs
          rw [← wrap] at decreased
          refine ⟨n,le_refl _,⟨?_,?_,?_,⟨keys,?_⟩,⟨stride,?_⟩,⟨key,?_⟩,?_,hashProbeNext index capacity,nextIndex,nextInside,
            by omega⟩,meta'.1⟩
          · rw [frame _ (by decide)]; exact capL
          · rw [frame _ (by decide)]; exact usedL
          · rw [frame _ (by decide)]; exact lenL
          · rw [frame _ (by decide)]; exact keysL
          · rw [frame _ (by decide)]; exact strideL
          · rw [frame _ (by decide)]; exact keyL
          · rw [memory,meta'.2.1,meta'.2.2.1]; exact emptyB
      · exact absurd cont (by
          have := evaluate_noTopContinue hashFindIteration (by decide) (decClockHOLFinite s)
          unfold hashFindIteration at this; exact this)
    · intro brk
      exact absurd brk (by
        have := evaluate_noTopBreak hashFindIteration (by decide) (decClockHOLFinite s)
        unfold hashFindIteration at this; exact this)

#print axioms hashFindLoop_run

theorem runBounded_header_load {F : Type} (state : PanSemStateFiniteExact 64 F)
    (name base : MlS) (pointer offset value : BitVec 64) (continuation : ProgHOL 64) {cost : Nat}
    (binding : state.locals.lookup base = some (.val (.word pointer)))
    (domain : state.memaddrs (pointer + offset)) (cell : state.memory (pointer + offset) = .word value)
    (inner : RunBounded (setVarHOLFinite name (.val (.word value)) state) continuation cost) :
    RunBounded state (.dec name .one (.load .one (hashLocalAddress base offset)) continuation) cost := by
  unfold RunBounded at inner ⊢
  rw [evaluate_header_load_scope state name base pointer offset value continuation binding domain cell]
  exact inner

/-- `htab_find_slot` from a state whose table header is readable (capacity a
power of two, key length at most the heap cap) and whose occupancy array has a
known empty slot spends at most klen / 8 + 9 + cap * (4 klen + 2) ticks in
every outcome; no key, array or alignment readability is assumed. -/
theorem evaluate_htabFindSlot_body_bounded {F : Type} (state : PanSemStateFiniteExact 64 F)
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
    (budget : keyLength.toNat / 8 + 8 + 1 + (capacity.toNat * (4 * keyLength.toNat + 1 + 0 + 1) + 0) ≤ state.clock) :
    RunBounded state (sourceFunctionBody Guest.guestFn_htab_find_slot)
      (keyLength.toNat / 8 + 8 + 1 + (capacity.toNat * (4 * keyLength.toNat + 1 + 0 + 1) + 0)) := by
  have names : ofString "cap" ≠ ofString "t" ∧ ofString "klen" ≠ ofString "t" ∧ ofString "stride" ≠ ofString "t" ∧
      ofString "keys" ≠ ofString "t" := by decide
  rw [source_htabFind_header_prefix]
  apply runBounded_header_load _ _ _ table 16 capacity _ tableLocal domain16 cell16
  apply runBounded_header_load _ _ _ table 0 keyLength _
    (by simp [setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,names.1,tableLocal]) (by exact domain0) (by exact cell0)
  apply runBounded_header_load _ _ _ table 8 stride _
    (by simp [setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,names.1,names.2.1,tableLocal]) (by exact domain8) (by exact cell8)
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
  have args : evalListHOLFinite loaded (h := fun a => Classical.propDecidable (loaded.memaddrs a))
      [.var .local (ofString "key"),.var .local (ofString "klen")] =
        some [.val (.word key),.val (.word keyLength)] := by
    rw [evalListHOLFinite_eq_toExact]
    simp [evalListHOLExact,evalHOLExact,keyL,lenL]
  unfold hashFindHashScope
  apply runBounded_htabHash_decCall loaded _ _ _ _ key keyLength loadedFacts.1 args (by omega)
    (by rw [loadedFacts.2.2.2.2]; exact budget)
  intro value post pc pm pa pb _ tc
  unfold hashFindIndexScope
  apply RunBounded.dec
  intro index evaluated
  generalize hresumed : setVarHOLFinite (ofString "h") value {post with locals := loaded.locals} = resumed at evaluated ⊢
  have resumedLookup : ∀ k, k ≠ ofString "h" → resumed.locals.lookup k = loaded.locals.lookup k := by
    intro k ne
    rw [← hresumed]
    simp [setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,Ne.symm ne]
  have valueL : resumed.locals.lookup (ofString "h") = some value := by
    rw [← hresumed]; simp [setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]
  cases value with
  | val word =>
    cases word with
    | word hash =>
      have hashL := valueL
      rw [eval_hashFind_initial_index resumed hash capacity hashL
        (by rw [resumedLookup _ (by decide)]; exact capL)] at evaluated
      cases evaluated
      generalize hentry : setVarHOLFinite (ofString "i") (.val (.word (hashFindInitialIndex hash capacity))) resumed = entry
      have entryLookup : ∀ k, k ≠ ofString "i" → k ≠ ofString "h" → entry.locals.lookup k = loaded.locals.lookup k := by
        intro k ni nh
        rw [← hentry]
        simp [setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,Ne.symm ni]
        exact resumedLookup k nh
      have entryFacts : entry.code = originalRuntimeCode ∧ entry.memory = state.memory ∧ entry.memaddrs = state.memaddrs ∧
          entry.be = state.be ∧ entry.clock = post.clock := by
        rw [← hentry,← hresumed]
        exact ⟨pc.trans loadedFacts.1,pm.trans loadedFacts.2.1,pa.trans loadedFacts.2.2.1,pb.trans loadedFacts.2.2.2.1,rfl⟩
      have range := hashFind_initial_index_bound hash capacity bits power
      have ranked : FindProbeRank capacity used empty keyLength entry capacity.toNat := by
        refine ⟨?_,?_,?_,⟨keys,?_⟩,⟨stride,?_⟩,⟨key,?_⟩,?_,hashFindInitialIndex hash capacity,?_,range.2,?_⟩
        · rw [entryLookup _ (by decide) (by decide)]; exact capL
        · rw [entryLookup _ (by decide) (by decide)]; exact usedL
        · rw [entryLookup _ (by decide) (by decide)]; exact lenL
        · rw [entryLookup _ (by decide) (by decide)]; exact keysL
        · rw [entryLookup _ (by decide) (by decide)]; exact strideL
        · rw [entryLookup _ (by decide) (by decide)]; exact keyL
        · rw [entryFacts.2.1,entryFacts.2.2.1,entryFacts.2.2.2.1]; exact emptyByte
        · rw [← hentry]; simp [setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]
        · exact Nat.le_of_lt (hashProbeDistance_lt_capacity _ _ _ range.2 emptyInside)
      unfold hashFindTail
      have loop := hashFindLoop_run capacity used empty keyLength bits power emptyInside small capacity.toNat entry
        entryFacts.1 ranked (by rw [entryFacts.2.2.2.2]; omega)
      refine RunBounded.seq ⟨loop.1,loop.2.1,loop.2.2.1⟩ (by rw [entryFacts.2.2.2.2]; omega) ?_
      intro final _ finalCode _
      exact RunBounded.ofProg (ProgBounded.straight _ (by decide)) (finalCode.trans entryFacts.1) (Nat.zero_le _)
  | _ =>
    have capR : resumed.locals.lookup (ofString "cap") = some (.val (.word capacity)) := by
      rw [resumedLookup _ (by decide)]; exact capL
    simp [hashFindIndexExpression,evalHOLExact,evalListHOLExact,valueL,capR,valueIsWord,wordOpHOL,wordOp,valueWord] at evaluated

#print axioms evaluate_htabFindSlot_body_bounded

/-- A declared `htab_find_slot` call on word arguments, from a caller whose
table header is readable with power-of-two capacity, key length at most the
heap cap and a known empty occupancy slot, costs
klen / 8 + 10 + cap * (4 klen + 2) plus its continuation in every outcome. -/
theorem runBounded_htabFindSlot_decCall {F : Type} (state : PanSemStateFiniteExact 64 F) (name : MlS)
    (tableArgument keyArgument : ExpHOL 64) (continuation : ProgHOL 64)
    (table key capacity keyLength stride keys used empty : BitVec 64) (bits : Nat)
    (code : state.code = originalRuntimeCode)
    (args : evalListHOLFinite state (h := fun a => Classical.propDecidable (state.memaddrs a))
      [tableArgument,keyArgument] = some [.val (.word table),.val (.word key)])
    (domain16 : state.memaddrs (table + 16)) (cell16 : state.memory (table + 16) = .word capacity)
    (domain0 : state.memaddrs (table + 0)) (cell0 : state.memory (table + 0) = .word keyLength)
    (domain8 : state.memaddrs (table + 8)) (cell8 : state.memory (table + 8) = .word stride)
    (domain32 : state.memaddrs (table + 32)) (cell32 : state.memory (table + 32) = .word keys)
    (domain48 : state.memaddrs (table + 48)) (cell48 : state.memory (table + 48) = .word used)
    (power : capacity.toNat = 2 ^ bits) (emptyInside : empty.toNat < capacity.toNat)
    (emptyByte : @panMemLoadByteHOL 64 _ state.memory state.memaddrs
      (fun a => Classical.propDecidable (state.memaddrs a)) state.be (used + empty) = some 0)
    (small : keyLength.toNat ≤ 33806089496) {tailCost : Nat}
    (budget : keyLength.toNat / 8 + 8 + 1 + (capacity.toNat * (4 * keyLength.toNat + 1 + 0 + 1) + 0) + 1 + tailCost ≤
      state.clock)
    (tail : ∀ value (post : PanSemStateFiniteExact 64 F), post.code = state.code → post.memaddrs = state.memaddrs →
      post.be = state.be → tailCost ≤ post.clock →
      RunBounded (setVarHOLFinite name value {post with locals := state.locals}) continuation tailCost) :
    RunBounded state (.decCall name .one (ofString "htab_find_slot") [tableArgument,keyArgument] continuation)
      (keyLength.toNat / 8 + 8 + 1 + (capacity.toNat * (4 * keyLength.toNat + 1 + 0 + 1) + 0) + 1 + tailCost) := by
  refine RunBounded.decCall args budget ?_
  intro body locals returnShape lookup
  have installed : state.code.lookup (ofString "htab_find_slot") =
      some ([(ofString "t",.one),(ofString "key",.one)],sourceFunctionBody Guest.guestFn_htab_find_slot,.one) := by
    rw [code]; exact originalRuntimeCode_hashFind_lookup
  rw [pan_two_word_lookup state.code.lookup (ofString "htab_find_slot") (ofString "t") (ofString "key")
    (sourceFunctionBody Guest.guestFn_htab_find_slot) table key (by decide) installed] at lookup
  cases lookup
  constructor
  · refine evaluate_htabFindSlot_body_bounded _ (by exact code) table key capacity keyLength stride keys used empty bits
      ?_ ?_ (by exact domain16) (by exact cell16) (by exact domain0) (by exact cell0) (by exact domain8) (by exact cell8)
      (by exact domain32) (by exact cell32) (by exact domain48) (by exact cell48) power emptyInside
      (by exact emptyByte) small ?_
    · simp [callEntryStateHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,show ofString "key" ≠ ofString "t" by decide]
    · simp [callEntryStateHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]
    · change _ ≤ state.clock - 1; omega
  · intro value post run tc
    have meta' := evaluateHOLFiniteState_metadata
      (callEntryStateHOLFinite state ((HolFiniteMapExact.empty.update (ofString "t",.val (.word table))).update
        (ofString "key",.val (.word key)))) (sourceFunctionBody Guest.guestFn_htab_find_slot)
    rw [run] at meta'
    exact tail value post meta'.1 meta'.2.1 meta'.2.2.1 tc

#print axioms runBounded_htabFindSlot_decCall
end InitECandidate.Runtime
