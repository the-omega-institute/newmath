import BEDC.Derived.PhilosophyCannotClaimRegistryUp.TasteGate

namespace BEDC.Derived.PhilosophyCannotClaimRegistryUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.Meta.TasteGate

theorem PhilosophyCannotClaimRegistryObligationBoundary
    (x : PhilosophyCannotClaimRegistryUp) :
    ∃ C S E U B H K P N : BHist,
      x = PhilosophyCannotClaimRegistryUp.mk C S E U B H K P N ∧
        philosophyCannotClaimRegistryFields x = [C, S, E, U, B, H, K, P, N] ∧
          Cont BHist.Empty C C ∧
            Cont BHist.Empty S S ∧
              Cont BHist.Empty E E ∧
                Cont BHist.Empty U U ∧
                  Cont BHist.Empty B B ∧
                    Cont BHist.Empty H H ∧
                      Cont BHist.Empty K K ∧
                        Cont BHist.Empty P P ∧
                          Cont BHist.Empty N N ∧
                            BHistCarrier.fromEventFlow
                                (BHistCarrier.toEventFlow x) =
                              some x := by
  -- BEDC touchpoint anchor: BHist Cont ChapterTasteGate
  cases x with
  | mk C S E U B H K P N =>
      exact
        ⟨C, S, E, U, B, H, K, P, N, rfl, rfl,
          cont_left_unit C,
          cont_left_unit S,
          cont_left_unit E,
          cont_left_unit U,
          cont_left_unit B,
          cont_left_unit H,
          cont_left_unit K,
          cont_left_unit P,
          cont_left_unit N,
          ChapterTasteGate.round_trip
            (X := PhilosophyCannotClaimRegistryUp)
            (PhilosophyCannotClaimRegistryUp.mk C S E U B H K P N)⟩

end BEDC.Derived.PhilosophyCannotClaimRegistryUp
