import InitECandidate.Proofs.CompactComputation
import InitECandidate.Proofs.SsaCheckpoints154.Proof2
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
open Flapjack Flapjack.Compiler.Backend
open InitECandidate.Proofs.SmallSsaKernelComputation
namespace InitECandidate.Proofs.SsaCheckpoints154
theorem node192_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_432 state64 453 state65 = (program26566,state1335,1525) := by
  unfold InitECandidate.Proofs.WordStages.word154_1_432
  rw [ssaStructural.eq_def]
  dsimp only
  rw [node190_eq, node191_eq]
  kernel_rfl
theorem node193_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_434 state1335 1525 state65 = (program26569,state1349,1533) := by
  kernel_rfl
theorem node194_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_435 state64 453 state65 = (program26570,state1349,1533) := by
  unfold InitECandidate.Proofs.WordStages.word154_1_435
  rw [ssaStructural.eq_def]
  dsimp only
  rw [node192_eq, node193_eq]
  kernel_rfl
theorem node195_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_0_225 state1349 1533 state65 = (InitECandidate.Proofs.WordStages.word154_2_660,state1355,1537) := by
  kernel_rfl
theorem node196_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_437 state64 453 state65 = (program26571,state1355,1537) := by
  unfold InitECandidate.Proofs.WordStages.word154_1_437
  rw [ssaStructural.eq_def]
  dsimp only
  rw [node194_eq, node195_eq]
  kernel_rfl
theorem node197_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_439 state1355 1537 state65 = (program26573,state1371,1545) := by
  kernel_rfl
theorem node198_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_440 state64 453 state65 = (program26574,state1371,1545) := by
  unfold InitECandidate.Proofs.WordStages.word154_1_440
  rw [ssaStructural.eq_def]
  dsimp only
  rw [node196_eq, node197_eq]
  kernel_rfl
theorem node199_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_0_229 state1371 1545 state65 = (InitECandidate.Proofs.WordStages.word154_2_666,state1379,1549) := by
  kernel_rfl
theorem node200_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_442 state64 453 state65 = (program26575,state1379,1549) := by
  unfold InitECandidate.Proofs.WordStages.word154_1_442
  rw [ssaStructural.eq_def]
  dsimp only
  rw [node198_eq, node199_eq]
  kernel_rfl
theorem node201_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_456 state1379 1549 state65 = (program26593,state1409,1589) := by
  kernel_rfl
theorem node202_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_457 state64 453 state65 = (program26594,state1409,1589) := by
  unfold InitECandidate.Proofs.WordStages.word154_1_457
  rw [ssaStructural.eq_def]
  dsimp only
  rw [node200_eq, node201_eq]
  kernel_rfl
theorem node203_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_459 state1409 1589 state65 = (program26597,state1423,1597) := by
  kernel_rfl
theorem node204_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_460 state64 453 state65 = (program26598,state1423,1597) := by
  unfold InitECandidate.Proofs.WordStages.word154_1_460
  rw [ssaStructural.eq_def]
  dsimp only
  rw [node202_eq, node203_eq]
  kernel_rfl
theorem node205_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_0_235 state1423 1597 state65 = (program26599,state1430,1601) := by
  kernel_rfl
theorem node206_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_462 state64 453 state65 = (program26600,state1430,1601) := by
  unfold InitECandidate.Proofs.WordStages.word154_1_462
  rw [ssaStructural.eq_def]
  dsimp only
  rw [node204_eq, node205_eq]
  kernel_rfl
theorem node207_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_464 state1430 1601 state65 = (program26603,state1445,1609) := by
  kernel_rfl
theorem node208_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_465 state64 453 state65 = (program26604,state1445,1609) := by
  unfold InitECandidate.Proofs.WordStages.word154_1_465
  rw [ssaStructural.eq_def]
  dsimp only
  rw [node206_eq, node207_eq]
  kernel_rfl
theorem node209_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_0_239 state1445 1609 state65 = (program26605,state1452,1613) := by
  kernel_rfl
theorem node210_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_467 state64 453 state65 = (program26606,state1452,1613) := by
  unfold InitECandidate.Proofs.WordStages.word154_1_467
  rw [ssaStructural.eq_def]
  dsimp only
  rw [node208_eq, node209_eq]
  kernel_rfl
theorem node211_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_469 state1452 1613 state65 = (program26609,state1468,1621) := by
  kernel_rfl
theorem node212_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_470 state64 453 state65 = (program26610,state1468,1621) := by
  unfold InitECandidate.Proofs.WordStages.word154_1_470
  rw [ssaStructural.eq_def]
  dsimp only
  rw [node210_eq, node211_eq]
  kernel_rfl
theorem node213_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_0_243 state1468 1621 state65 = (program26611,state1476,1625) := by
  kernel_rfl
theorem node214_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_472 state64 453 state65 = (program26612,state1476,1625) := by
  unfold InitECandidate.Proofs.WordStages.word154_1_472
  rw [ssaStructural.eq_def]
  dsimp only
  rw [node212_eq, node213_eq]
  kernel_rfl
theorem node215_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_474 state1476 1625 state65 = (program26615,state1488,1633) := by
  kernel_rfl
theorem node216_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_475 state64 453 state65 = (program26616,state1488,1633) := by
  unfold InitECandidate.Proofs.WordStages.word154_1_475
  rw [ssaStructural.eq_def]
  dsimp only
  rw [node214_eq, node215_eq]
  kernel_rfl
theorem node217_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_0_247 state1488 1633 state65 = (program26617,state1493,1637) := by
  kernel_rfl
theorem node218_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_477 state64 453 state65 = (program26618,state1493,1637) := by
  unfold InitECandidate.Proofs.WordStages.word154_1_477
  rw [ssaStructural.eq_def]
  dsimp only
  rw [node216_eq, node217_eq]
  kernel_rfl
theorem node219_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_491 state1493 1637 state65 = (program26637,state1525,1677) := by
  kernel_rfl
theorem node220_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_492 state64 453 state65 = (program26638,state1525,1677) := by
  unfold InitECandidate.Proofs.WordStages.word154_1_492
  rw [ssaStructural.eq_def]
  dsimp only
  rw [node218_eq, node219_eq]
  kernel_rfl
theorem node221_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_494 state1525 1677 state65 = (program26641,state1540,1685) := by
  kernel_rfl
theorem node222_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_495 state64 453 state65 = (program26642,state1540,1685) := by
  unfold InitECandidate.Proofs.WordStages.word154_1_495
  rw [ssaStructural.eq_def]
  dsimp only
  rw [node220_eq, node221_eq]
  kernel_rfl
theorem node223_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_0_253 state1540 1685 state65 = (program26643,state1547,1689) := by
  kernel_rfl
theorem node224_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_497 state64 453 state65 = (program26644,state1547,1689) := by
  unfold InitECandidate.Proofs.WordStages.word154_1_497
  rw [ssaStructural.eq_def]
  dsimp only
  rw [node222_eq, node223_eq]
  kernel_rfl
theorem node225_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_499 state1547 1689 state65 = (program26647,state1563,1697) := by
  kernel_rfl
theorem node226_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_500 state64 453 state65 = (program26648,state1563,1697) := by
  unfold InitECandidate.Proofs.WordStages.word154_1_500
  rw [ssaStructural.eq_def]
  dsimp only
  rw [node224_eq, node225_eq]
  kernel_rfl
theorem node227_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_0_257 state1563 1697 state65 = (program26649,state1571,1701) := by
  kernel_rfl
theorem node228_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_502 state64 453 state65 = (program26650,state1571,1701) := by
  unfold InitECandidate.Proofs.WordStages.word154_1_502
  rw [ssaStructural.eq_def]
  dsimp only
  rw [node226_eq, node227_eq]
  kernel_rfl
theorem node229_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_504 state1571 1701 state65 = (program26653,state1584,1709) := by
  kernel_rfl
theorem node230_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_505 state64 453 state65 = (program26654,state1584,1709) := by
  unfold InitECandidate.Proofs.WordStages.word154_1_505
  rw [ssaStructural.eq_def]
  dsimp only
  rw [node228_eq, node229_eq]
  kernel_rfl
theorem node231_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_0_261 state1584 1709 state65 = (program26655,state1590,1713) := by
  kernel_rfl
theorem node232_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_507 state64 453 state65 = (program26656,state1590,1713) := by
  unfold InitECandidate.Proofs.WordStages.word154_1_507
  rw [ssaStructural.eq_def]
  dsimp only
  rw [node230_eq, node231_eq]
  kernel_rfl
theorem node233_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_509 state1590 1713 state65 = (program26659,state1605,1721) := by
  kernel_rfl
theorem node234_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_510 state64 453 state65 = (program26660,state1605,1721) := by
  unfold InitECandidate.Proofs.WordStages.word154_1_510
  rw [ssaStructural.eq_def]
  dsimp only
  rw [node232_eq, node233_eq]
  kernel_rfl
theorem node235_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_0_265 state1605 1721 state65 = (program26661,state1613,1725) := by
  kernel_rfl
theorem node236_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_512 state64 453 state65 = (program26662,state1613,1725) := by
  unfold InitECandidate.Proofs.WordStages.word154_1_512
  rw [ssaStructural.eq_def]
  dsimp only
  rw [node234_eq, node235_eq]
  kernel_rfl
theorem node237_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_526 state1613 1725 state65 = (program26681,state1646,1765) := by
  kernel_rfl
theorem node238_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_527 state64 453 state65 = (program26682,state1646,1765) := by
  unfold InitECandidate.Proofs.WordStages.word154_1_527
  rw [ssaStructural.eq_def]
  dsimp only
  rw [node236_eq, node237_eq]
  kernel_rfl
theorem node239_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_529 state1646 1765 state65 = (program26685,state1662,1773) := by
  kernel_rfl
theorem node240_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_530 state64 453 state65 = (program26686,state1662,1773) := by
  unfold InitECandidate.Proofs.WordStages.word154_1_530
  rw [ssaStructural.eq_def]
  dsimp only
  rw [node238_eq, node239_eq]
  kernel_rfl
theorem node241_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_0_271 state1662 1773 state65 = (program26687,state1670,1777) := by
  kernel_rfl
theorem node242_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_532 state64 453 state65 = (program26688,state1670,1777) := by
  unfold InitECandidate.Proofs.WordStages.word154_1_532
  rw [ssaStructural.eq_def]
  dsimp only
  rw [node240_eq, node241_eq]
  kernel_rfl
theorem node243_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_534 state1670 1777 state65 = (program26691,state1682,1785) := by
  kernel_rfl
theorem node244_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_535 state64 453 state65 = (program26692,state1682,1785) := by
  unfold InitECandidate.Proofs.WordStages.word154_1_535
  rw [ssaStructural.eq_def]
  dsimp only
  rw [node242_eq, node243_eq]
  kernel_rfl
theorem node245_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_0_275 state1682 1785 state65 = (program26693,state1686,1789) := by
  kernel_rfl
theorem node246_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_537 state64 453 state65 = (program26694,state1686,1789) := by
  unfold InitECandidate.Proofs.WordStages.word154_1_537
  rw [ssaStructural.eq_def]
  dsimp only
  rw [node244_eq, node245_eq]
  kernel_rfl
theorem node247_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_539 state1686 1789 state65 = (program26697,state1701,1797) := by
  kernel_rfl
theorem node248_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_540 state64 453 state65 = (program26698,state1701,1797) := by
  unfold InitECandidate.Proofs.WordStages.word154_1_540
  rw [ssaStructural.eq_def]
  dsimp only
  rw [node246_eq, node247_eq]
  kernel_rfl
theorem node249_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_0_279 state1701 1797 state65 = (program26699,state1708,1801) := by
  kernel_rfl
theorem node250_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_542 state64 453 state65 = (program26700,state1708,1801) := by
  unfold InitECandidate.Proofs.WordStages.word154_1_542
  rw [ssaStructural.eq_def]
  dsimp only
  rw [node248_eq, node249_eq]
  kernel_rfl
theorem node251_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_544 state1708 1801 state65 = (program26703,state1721,1809) := by
  kernel_rfl
theorem node252_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_545 state64 453 state65 = (program26704,state1721,1809) := by
  unfold InitECandidate.Proofs.WordStages.word154_1_545
  rw [ssaStructural.eq_def]
  dsimp only
  rw [node250_eq, node251_eq]
  kernel_rfl
theorem node253_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_0_283 state1721 1809 state65 = (program26705,state1727,1813) := by
  kernel_rfl
theorem node254_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_547 state64 453 state65 = (program26706,state1727,1813) := by
  unfold InitECandidate.Proofs.WordStages.word154_1_547
  rw [ssaStructural.eq_def]
  dsimp only
  rw [node252_eq, node253_eq]
  kernel_rfl
theorem node255_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_561 state1727 1813 state65 = (program26725,state1759,1853) := by
  kernel_rfl
end InitECandidate.Proofs.SsaCheckpoints154
