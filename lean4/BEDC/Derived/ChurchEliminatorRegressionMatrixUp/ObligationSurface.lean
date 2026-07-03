import BEDC.Derived.ChurchEliminatorRegressionMatrixUp.TasteGate
import BEDC.FKernel.Cont

namespace BEDC.Derived.ChurchEliminatorRegressionMatrixUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.Meta.TasteGate

theorem ChurchEliminatorRegressionMatrix_obligation_surface
    (x : ChurchEliminatorRegressionMatrixUp) :
    ∃ F G L C B S X H K P N familyRead betaRead spendRead : BHist,
      x = ChurchEliminatorRegressionMatrixUp.mk F G L C B S X H K P N ∧
        List.Mem (churchEliminatorRegressionMatrixEncodeBHist F) (BHistCarrier.toEventFlow x) ∧
        List.Mem (churchEliminatorRegressionMatrixEncodeBHist C) (BHistCarrier.toEventFlow x) ∧
        List.Mem (churchEliminatorRegressionMatrixEncodeBHist B) (BHistCarrier.toEventFlow x) ∧
        Cont F G familyRead ∧
        Cont C B betaRead ∧
        Cont S X spendRead ∧
        hsame H H ∧ hsame K K ∧ hsame P P ∧ hsame N N := by
  -- BEDC touchpoint anchor: BHist BMark BHistCarrier Cont hsame
  cases x with
  | mk F G L C B S X H K P N =>
      refine
        ⟨F, G, L, C, B, S, X, H, K, P, N, append F G, append C B, append S X,
          rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · exact List.Mem.tail _ (List.Mem.head _)
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
      · rfl
      · rfl
      · rfl
      · exact hsame_refl H
      · exact hsame_refl K
      · exact hsame_refl P
      · exact hsame_refl N

end BEDC.Derived.ChurchEliminatorRegressionMatrixUp
