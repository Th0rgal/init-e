import InitECandidate.Runtime.FrameNewFundingStores
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

theorem source_frame_new_0 : frameNewAt 0=.decCall (ofString "stack_mark") .one (ofString "scratch_mark") [] (frameNewAt 1) := rfl
theorem source_frame_new_1 : frameNewAt 1=.decCall (ofString "mem_mark") .one (ofString "frame_mem_mark") [] (frameNewAt 2) := rfl
theorem source_frame_new_2 : frameNewAt 2=.decCall (ofString "e") .one (ofString "scratch_alloc") [.const 280] (frameNewAt 3) := rfl
theorem source_frame_new_3 : frameNewAt 3=.seq (.call (some (none,none)) (ofString "memzero") [.var .local (ofString "e"),.const 280]) (frameNewAt 4) := rfl
theorem source_frame_new_4 : frameNewAt 4=.decCall (ofString "stk") .one (ofString "scratch_alloc") [.panop .mul [.const 32,.const 32]] (frameNewAt 5) := rfl
theorem source_frame_new_5 : frameNewAt 5=
 .seq (.store (frameNewLocalAddress (ofString "e") 208) (.var .local (ofString "stack_mark")))
  (.seq (.store (frameNewLocalAddress (ofString "e") 8) (.var .local (ofString "stk")))
   (.seq (.store (frameNewLocalAddress (ofString "e") 232) (.const 32)) (frameNewAt 8))) := rfl
theorem source_frame_new_8 : frameNewAt 8=.decCall (ofString "mem") .one (ofString "frame_mem_alloc") [.const 1024] (frameNewAt 9) := rfl
theorem source_frame_new_9 : frameNewAt 9=
 .seq (.store (frameNewLocalAddress (ofString "e") 224) (.var .local (ofString "mem_mark")))
  (.seq (.store (frameNewLocalAddress (ofString "e") 24) (.var .local (ofString "mem")))
   (.seq (.store (frameNewLocalAddress (ofString "e") 40) (.const 1024)) (frameNewAt 12))) := rfl
theorem source_frame_new_12 : frameNewAt 12=
 .seq (.store (frameNewLocalAddress (ofString "e") 48) (.load .one (frameNewLocalAddress (ofString "msg") 112)))
  (.seq (.store (frameNewLocalAddress (ofString "e") 56) (.load .one (frameNewLocalAddress (ofString "msg") 120))) (frameNewAt 14)) := rfl
theorem source_frame_new_16 : frameNewAt 16=.decCall (ofString "jd") .one (ofString "compute_jumpdests")
 [.load .one (frameNewLocalAddress (ofString "msg") 112),.load .one (frameNewLocalAddress (ofString "msg") 120)] (frameNewAt 17) := rfl
theorem source_frame_new_17 : frameNewAt 17=.seq (.store (frameNewLocalAddress (ofString "e") 80) (.var .local (ofString "jd"))) (frameNewAt 18) := rfl
theorem source_frame_new_18 : frameNewAt 18=.decCall (ofString "logs") .one (ofString "lst_new_scratch") [.const 8,.const 4] (frameNewAt 19) := rfl
theorem source_frame_new_19 : frameNewAt 19=
 .seq (.store (frameNewLocalAddress (ofString "e") 88) (.var .local (ofString "logs")))
  (.seq (.store (frameNewLocalAddress (ofString "e") 104) (.const 1))
   (.seq (.store (frameNewLocalAddress (ofString "e") 112) (.var .local (ofString "msg"))) (frameNewAt 22))) := rfl
theorem source_frame_new_22 : frameNewAt 22=.decCall (ofString "del") .one (ofString "htab_new_scratch") [.const 20,.const 4] (frameNewAt 23) := rfl
theorem source_frame_new_23 : frameNewAt 23=
 .seq (.store (frameNewLocalAddress (ofString "e") 136) (.var .local (ofString "del")))
  (.seq (.store (frameNewLocalAddress (ofString "e") 168) (.load .one (frameNewLocalAddress (ofString "msg") 152)))
   (.seq (.store (frameNewLocalAddress (ofString "e") 176) (.load .one (frameNewLocalAddress (ofString "msg") 160))) (frameNewAt 26))) := rfl
theorem source_frame_new_26 : frameNewAt 26=.decCall (ofString "acc_n") .one (ofString "htab_count")
 [.load .one (frameNewLocalAddress (ofString "msg") 152)] (frameNewAt 27) := rfl
theorem source_frame_new_27 : frameNewAt 27=.seq (.store (frameNewLocalAddress (ofString "e") 264) (.var .local (ofString "acc_n"))) (frameNewAt 28) := rfl
theorem source_frame_new_28 : frameNewAt 28=.seq (.call (some (some (.local,ofString "acc_n"),none)) (ofString "htab_count")
 [.load .one (frameNewLocalAddress (ofString "msg") 160)]) (frameNewAt 29) := rfl
theorem source_frame_new_29 : frameNewAt 29=
 .seq (.store (frameNewLocalAddress (ofString "e") 272) (.var .local (ofString "acc_n")))
  (.seq (.store (frameNewLocalAddress (ofString "e") 120) (.var .global (ofString "evm_empty")))
   (.seq (.store (frameNewLocalAddress (ofString "e") 144) (.var .global (ofString "evm_empty")))
    (.seq (.store (frameNewLocalAddress (ofString "e") 216) (.const 0)) (frameNewAt 33)))) := rfl
theorem source_frame_new_33 : frameNewAt 33=.return (.var .local (ofString "e")) := rfl
#print axioms source_frame_new_0
#print axioms source_frame_new_1
#print axioms source_frame_new_2
#print axioms source_frame_new_3
#print axioms source_frame_new_4
#print axioms source_frame_new_5
#print axioms source_frame_new_8
#print axioms source_frame_new_9
#print axioms source_frame_new_12
#print axioms source_frame_new_16
#print axioms source_frame_new_17
#print axioms source_frame_new_18
#print axioms source_frame_new_19
#print axioms source_frame_new_22
#print axioms source_frame_new_23
#print axioms source_frame_new_26
#print axioms source_frame_new_27
#print axioms source_frame_new_28
#print axioms source_frame_new_29
#print axioms source_frame_new_33
end InitECandidate.Runtime
