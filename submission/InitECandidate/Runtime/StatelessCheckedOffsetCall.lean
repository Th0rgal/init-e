import InitECandidate.Runtime.StatelessHeapGrowth
import InitECandidate.Runtime.LoadOneRead
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem ret_checkCall_checked {F : Type} (t post : PanSemStateFiniteExact 64 F) (rest : ProgHOL 64) (offsets WL : BitVec 64)
    (v : ValueHOL 64) (code : t.code = originalRuntimeCode)
    (hg : t.globals.lookup (ofString "ssz_offs") = some (.val (.word offsets)))
    (hwl : t.locals.lookup (ofString "wlen") = some (.val (.word WL)))
    (run : evaluateHOLFiniteState t (.seq statelessWitnessCheckCall rest) = (some (.returned v), post)) :
    ∃ t', evaluateHOLFiniteState t' rest = (some (.returned v), post) ∧ t'.locals = t.locals ∧
      t'.globals = t.globals ∧ t'.code = t.code ∧
      t'.memory=t.memory ∧t'.memaddrs=t.memaddrs ∧SszCheckOffsetsReturned t' offsets 3 12 WL (.val (.word 0)) := by
  have args : evalListHOLFinite t (h := fun address => Classical.propDecidable (t.memaddrs address))
      statelessWitnessCheckArguments =
      some [.val (.word offsets), .val (.word 3), .val (.word 12), .val (.word WL)] := by
    simp [statelessWitnessCheckArguments, evalListHOLFinite, evalListHOLExact, evalHOLExact, hg, hwl]
  rw [evaluateHOLFiniteState_seq_line780] at run
  cases callRun : evaluateHOLFiniteState t statelessWitnessCheckCall with
  | mk r t' =>
    rw [callRun] at run
    cases r with
    | some x =>
      have nr := evaluate_discard_call_no_return t (ofString "ssz_check_offsets") statelessWitnessCheckArguments v
      unfold statelessWitnessCheckCall at callRun
      rw [callRun] at nr
      exact absurd (Prod.mk.inj run).1 nr
    | none =>
      dsimp only at run
      obtain ⟨checked, memory, eg, domain, el⟩ := sszCheckOffsets_call_returned t _ offsets 3 12 WL args code (by decide) t'
        (by unfold statelessWitnessCheckCall at callRun; exact callRun)
      have mt := evaluateHOLFiniteState_metadata t statelessWitnessCheckCall
      rw [callRun] at mt
      exact ⟨t',run,el,eg,mt.1,memory,domain,sszCheckOffsetsReturned_congr t t' offsets 3 12 WL _ memory.symm domain.symm checked⟩

theorem eval_load_word_mem_at {F : Type} (state : PanSemStateFiniteExact 64 F) (expression : ExpHOL 64) (address value : BitVec 64)
    (pointer : @evalHOLExact 64 F _ state.toExact (fun a=>Classical.propDecidable (state.memaddrs a)) expression=some (.val (.word address)))
    (loaded : @evalHOLExact 64 F _ state.toExact (fun a=>Classical.propDecidable (state.memaddrs a)) (.load .one expression)=some (.val (.word value))) :
    memWord state.memory address=value := by
  obtain ⟨actual,word,atPointer,_,cell,valueEq⟩:=eval_load_one_read state expression _ loaded
  rw [pointer] at atPointer
  have pointerEq : address=actual := by simpa only [Option.some.injEq,ValueHOL.val.injEq,HolWordLab.word.injEq] using atPointer
  subst actual
  have wordEq : value=word := by simpa only [ValueHOL.val.injEq,HolWordLab.word.injEq] using valueEq
  subst word
  simp only [memWord,cell]
#print axioms eval_load_word_mem_at
#print axioms ret_checkCall_checked
end InitECandidate.Runtime
