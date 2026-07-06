import BEDC.Derived.ChurchEliminatorRegressionMatrixUp.TasteGate

namespace BEDC.Derived.ChurchEliminatorRegressionMatrixUp

open BEDC.FKernel.Hist
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

theorem ChurchEliminatorRegressionMatrixNameCertObligations
    (x : ChurchEliminatorRegressionMatrixUp) :
    ∃ F G L C B S X H K P N : BHist,
      x = ChurchEliminatorRegressionMatrixUp.mk F G L C B S X H K P N ∧
        List.Mem (churchEliminatorRegressionMatrixEncodeBHist F) (BHistCarrier.toEventFlow x) ∧
        List.Mem (churchEliminatorRegressionMatrixEncodeBHist G) (BHistCarrier.toEventFlow x) ∧
        List.Mem (churchEliminatorRegressionMatrixEncodeBHist L) (BHistCarrier.toEventFlow x) ∧
        List.Mem (churchEliminatorRegressionMatrixEncodeBHist C) (BHistCarrier.toEventFlow x) ∧
        List.Mem (churchEliminatorRegressionMatrixEncodeBHist B) (BHistCarrier.toEventFlow x) ∧
        List.Mem (churchEliminatorRegressionMatrixEncodeBHist S) (BHistCarrier.toEventFlow x) ∧
        hsame X X ∧ hsame H H ∧ hsame K K ∧ hsame P P ∧ hsame N N := by
  -- BEDC touchpoint anchor: BHist BMark BHistCarrier hsame
  cases x with
  | mk F G L C B S X H K P N =>
      refine
        ⟨F, G, L, C, B, S, X, H, K, P, N, rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
          ?_, ?_, ?_⟩
      · exact List.Mem.tail _ (List.Mem.head _)
      · exact List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))
      · exact
          List.Mem.tail _
            (List.Mem.tail _
              (List.Mem.tail _
                (List.Mem.tail _
                  (List.Mem.tail _ (List.Mem.head _)))))
      · exact
          List.Mem.tail _
            (List.Mem.tail _
              (List.Mem.tail _
                (List.Mem.tail _
                  (List.Mem.tail _
                    (List.Mem.tail _
                      (List.Mem.tail _ (List.Mem.head _)))))))
      · exact
          List.Mem.tail _
            (List.Mem.tail _
              (List.Mem.tail _
                (List.Mem.tail _
                  (List.Mem.tail _
                    (List.Mem.tail _
                      (List.Mem.tail _
                        (List.Mem.tail _
                          (List.Mem.tail _ (List.Mem.head _)))))))))
      · exact
          List.Mem.tail _
            (List.Mem.tail _
              (List.Mem.tail _
                (List.Mem.tail _
                  (List.Mem.tail _
                    (List.Mem.tail _
                      (List.Mem.tail _
                        (List.Mem.tail _
                          (List.Mem.tail _
                            (List.Mem.tail _
                              (List.Mem.tail _ (List.Mem.head _)))))))))))
      · exact hsame_refl X
      · exact hsame_refl H
      · exact hsame_refl K
      · exact hsame_refl P
      · exact hsame_refl N

theorem ChurchEliminatorRegressionMatrixCarrier_nonescape
    (x : ChurchEliminatorRegressionMatrixUp) :
    ∃ F G L C B S X H K P N : BHist,
      x = ChurchEliminatorRegressionMatrixUp.mk F G L C B S X H K P N ∧
        BHistCarrier.toEventFlow x =
          churchEliminatorRegressionMatrixToEventFlow
            (ChurchEliminatorRegressionMatrixUp.mk F G L C B S X H K P N) ∧
        List.Mem (churchEliminatorRegressionMatrixEncodeBHist K)
          (BHistCarrier.toEventFlow x) ∧
        List.Mem (churchEliminatorRegressionMatrixEncodeBHist P)
          (BHistCarrier.toEventFlow x) ∧
        List.Mem (churchEliminatorRegressionMatrixEncodeBHist N)
          (BHistCarrier.toEventFlow x) ∧
        churchEliminatorRegressionMatrixEncodeBHist BHist.Empty = ([] : RawEvent) := by
  -- BEDC touchpoint anchor: BHist BMark BHistCarrier
  cases x with
  | mk F G L C B S X H K P N =>
      refine ⟨F, G, L, C, B, S, X, H, K, P, N, rfl, rfl, ?_, ?_, ?_, rfl⟩
      · exact
          List.Mem.tail _
            (List.Mem.tail _
              (List.Mem.tail _
                (List.Mem.tail _
                  (List.Mem.tail _
                    (List.Mem.tail _
                      (List.Mem.tail _
                        (List.Mem.tail _
                          (List.Mem.tail _
                            (List.Mem.tail _
                              (List.Mem.tail _
                                (List.Mem.tail _
                                  (List.Mem.tail _
                                    (List.Mem.tail _
                                      (List.Mem.tail _
                                        (List.Mem.tail _
                                          (List.Mem.tail _ (List.Mem.head _)))))))))))))))))
      · exact
          List.Mem.tail _
            (List.Mem.tail _
              (List.Mem.tail _
                (List.Mem.tail _
                  (List.Mem.tail _
                    (List.Mem.tail _
                      (List.Mem.tail _
                        (List.Mem.tail _
                          (List.Mem.tail _
                            (List.Mem.tail _
                              (List.Mem.tail _
                                (List.Mem.tail _
                                  (List.Mem.tail _
                                    (List.Mem.tail _
                                      (List.Mem.tail _
                                        (List.Mem.tail _
                                          (List.Mem.tail _
                                            (List.Mem.tail _
                                              (List.Mem.tail _ (List.Mem.head _)))))))))))))))))))
      · exact
          List.Mem.tail _
            (List.Mem.tail _
              (List.Mem.tail _
                (List.Mem.tail _
                  (List.Mem.tail _
                    (List.Mem.tail _
                      (List.Mem.tail _
                        (List.Mem.tail _
                          (List.Mem.tail _
                            (List.Mem.tail _
                              (List.Mem.tail _
                                (List.Mem.tail _
                                  (List.Mem.tail _
                                    (List.Mem.tail _
                                      (List.Mem.tail _
                                        (List.Mem.tail _
                                          (List.Mem.tail _
                                            (List.Mem.tail _
                                              (List.Mem.tail _
                                                (List.Mem.tail _
                                                  (List.Mem.tail _
                                                    (List.Mem.head _)))))))))))))))))))))

end BEDC.Derived.ChurchEliminatorRegressionMatrixUp
