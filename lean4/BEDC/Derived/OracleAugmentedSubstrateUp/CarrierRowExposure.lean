import BEDC.Derived.OracleAugmentedSubstrateUp.TasteGate
import BEDC.FKernel.Cont
import BEDC.FKernel.Unary

namespace BEDC.Derived.OracleAugmentedSubstrateUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Unary

theorem OracleAugmentedSubstrateCarrier_carrier_row_exposure
    {S A T B E H C P N callRead transcriptRead boundaryRead evidenceRead namedRead : BHist} :
    UnaryHistory S →
      UnaryHistory A →
        UnaryHistory T →
          UnaryHistory B →
            UnaryHistory E →
              UnaryHistory N →
                Cont S A callRead →
                  Cont callRead T transcriptRead →
                    Cont transcriptRead B boundaryRead →
                      Cont boundaryRead E evidenceRead →
                        Cont evidenceRead N namedRead →
                          oracleAugmentedSubstrateFields
                              (OracleAugmentedSubstrateUp.mk S A T B E H C P N) =
                            [S, A, T, B, E, H, C, P, N] ∧
                            UnaryHistory callRead ∧
                              UnaryHistory transcriptRead ∧
                                UnaryHistory boundaryRead ∧
                                  UnaryHistory evidenceRead ∧
                                    UnaryHistory namedRead := by
  -- BEDC touchpoint anchor: BHist Cont UnaryHistory
  intro sUnary aUnary tUnary bUnary eUnary nUnary callRoute transcriptRoute
    boundaryRoute evidenceRoute nameRoute
  have callUnary : UnaryHistory callRead :=
    unary_cont_closed sUnary aUnary callRoute
  have transcriptUnary : UnaryHistory transcriptRead :=
    unary_cont_closed callUnary tUnary transcriptRoute
  have boundaryUnary : UnaryHistory boundaryRead :=
    unary_cont_closed transcriptUnary bUnary boundaryRoute
  have evidenceUnary : UnaryHistory evidenceRead :=
    unary_cont_closed boundaryUnary eUnary evidenceRoute
  have namedUnary : UnaryHistory namedRead :=
    unary_cont_closed evidenceUnary nUnary nameRoute
  exact ⟨rfl, callUnary, transcriptUnary, boundaryUnary, evidenceUnary, namedUnary⟩

end BEDC.Derived.OracleAugmentedSubstrateUp
