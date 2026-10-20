import InitECandidate.Runtime.KeyToNibblesUniformCallBound
import InitECandidate.Runtime.AllocationUniformBound
import InitECandidate.Runtime.HtabGrowRehash
import InitECandidate.Runtime.RunBounded
import InitECandidate.Runtime.RunAttemptHeadersSource
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

def mptNibbleUnsecuredTail : ProgHOL 64:=
 match structuralFunctionBody Guest.guestFn_mpt_nibble_key with | .seq _ tail=>tail | _=>.skip

def mptNibbleUnsecuredReturn : ProgHOL 64:=
 .return (.rstruct [.var .local (ofString "nb2"),.panop .mul [.const 2,.var .local (ofString "klen")]])

theorem source_mpt_nibble_unsecured_tail : mptNibbleUnsecuredTail=
 .decCall (ofString "nb2") .one (ofString "alloc") [.panop .mul [.const 2,.var .local (ofString "klen")]]
  (.seq (.call (some (none,none)) (ofString "key_to_nibbles")
   [.var .local (ofString "key"),.var .local (ofString "klen"),.var .local (ofString "nb2")]) mptNibbleUnsecuredReturn) := rfl

/-- The actual unsecured allocation/conversion suffix is input-linear even
when allocation or byte access fails. No room or readable key/output memory
is assumed; the real returned allocator supplies its typed output pointer. -/
theorem mpt_nibble_unsecured_tail_bounded {F : Type} (s : PanSemStateFiniteExact 64 F)
 (key length pointer : BitVec 64)
 (atKey : s.locals.lookup (ofString "key")=some (.val (.word key)))
 (atLength : s.locals.lookup (ofString "klen")=some (.val (.word length)))
 (atHeap : s.globals.lookup (ofString "heap_ptr")=some (.val (.word pointer)))
 (small : length.toNat+4<2^64) (code : s.code=originalRuntimeCode)
 (budget : 1+1+(length.toNat/4+4)≤s.clock) :
 RunBounded s mptNibbleUnsecuredTail (1+1+(length.toNat/4+4)) := by
 rw [source_mpt_nibble_unsecured_tail]
 have args : evalListHOLFinite s (h:=fun a=>Classical.propDecidable (s.memaddrs a))
  [.panop .mul [.const 2,.var .local (ofString "klen")]]=some [.val (.word (2#64*length))] := by
  simp [evalListHOLFinite,evalListHOLExact,evalHOLExact,atLength,panOpHOL,valueIsWord,valueWord]
 have installed : s.code.lookup (ofString "alloc")=some ([(ofString "n",.one)],sourceFunctionBody Guest.guestFn_alloc,.one) := by
  rw [code];exact originalRuntimeCode_allocation_lookup
 have lookup:=pan_single_word_lookup s.code.lookup (ofString "alloc") (ofString "n")
  (sourceFunctionBody Guest.guestFn_alloc) (2#64*length) installed
 apply RunBounded.decCall (bodyCost:=1) (tailCost:=length.toNat/4+4) args budget
 intro body callee shape actual
 rw [lookup] at actual
 obtain ⟨rfl,rfl,rfl⟩:=Option.some.inj actual |>.symm
 let entry:=callEntryStateHOLFinite s (HolFiniteMapExact.empty.update (ofString "n",.val (.word (2#64*length))))
 have allocator:=evaluate_source_alloc_uniform_bounded entry code (by change 1≤s.clock-1;omega)
 refine ⟨⟨allocator.1,allocator.2.1,allocator.2.2.1⟩,?_⟩
 intro value post run ticks
 have atSize : entry.locals.lookup (ofString "n")=some (.val (.word (2#64*length))) := by
  simp [entry,callEntryStateHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]
 obtain ⟨request,finish,returned,memory,domain,endian,installedKept,globals⟩:=
  alloc_body_returned entry post pointer (2#64*length) code atHeap atSize value run
 let next:=setVarHOLFinite (ofString "nb2") value {post with locals:=s.locals}
 have nextKey : next.locals.lookup (ofString "key")=some (.val (.word key)) := by
  simpa (config:={decide:=true}) [next,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE] using atKey
 have nextLength : next.locals.lookup (ofString "klen")=some (.val (.word length)) := by
  simpa (config:={decide:=true}) [next,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE] using atLength
 have nextOutput : next.locals.lookup (ofString "nb2")=some (.val (.word pointer)) := by
  simp [next,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,returned]
 have nextCode : next.code=originalRuntimeCode:=installedKept.trans code
 have conversionArgs : evalListHOLFinite next (h:=fun a=>Classical.propDecidable (next.memaddrs a))
  [.var .local (ofString "key"),.var .local (ofString "klen"),.var .local (ofString "nb2")]=
  some [.val (.word key),.val (.word length),.val (.word pointer)] := by
  simp [evalListHOLFinite,evalListHOLExact,evalHOLExact,nextKey,nextLength,nextOutput]
 have conversion : RunBounded next (.call (some (none,none)) (ofString "key_to_nibbles")
  [.var .local (ofString "key"),.var .local (ofString "klen"),.var .local (ofString "nb2")]) (length.toNat/4+4) :=
  evaluate_keyToNibbles_call_uniform_bounded next _ _ _ key pointer length small nextCode conversionArgs ticks
 have sequence:=RunBounded.seq (b:=0) conversion (by change length.toNat/4+4+0≤post.clock;omega)
  (fun after normal kept remaining=>RunBounded.ofProg (ProgBounded.straight mptNibbleUnsecuredReturn rfl)
   (kept.trans nextCode) remaining)
 simpa only [Nat.add_zero] using sequence
#print axioms source_mpt_nibble_unsecured_tail
#print axioms mpt_nibble_unsecured_tail_bounded
end InitECandidate.Runtime
