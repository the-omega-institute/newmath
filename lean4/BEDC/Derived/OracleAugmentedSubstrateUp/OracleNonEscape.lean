import BEDC.Derived.OracleAugmentedSubstrateUp.TasteGate
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.OracleAugmentedSubstrateUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem OracleAugmentedSubstrateCarrier_oracle_nonescape
    {S A T B E H N callRead transcriptRead boundaryRead evidenceRead namedRead : BHist} :
    UnaryHistory S →
      UnaryHistory A →
        UnaryHistory T →
          UnaryHistory B →
            UnaryHistory E →
              UnaryHistory H →
                UnaryHistory N →
                  Cont S A callRead →
                    Cont callRead T transcriptRead →
                      Cont transcriptRead B boundaryRead →
                        Cont boundaryRead E evidenceRead →
                          Cont evidenceRead N namedRead →
                            SemanticNameCert
                                (fun row : BHist => hsame row namedRead ∧ UnaryHistory row)
                                (fun row : BHist =>
                                  hsame row S ∨ hsame row A ∨ hsame row T ∨
                                    hsame row B ∨ hsame row E ∨ hsame row H ∨
                                      hsame row N ∨ hsame row callRead ∨
                                        hsame row transcriptRead ∨ hsame row boundaryRead ∨
                                          hsame row evidenceRead ∨ hsame row namedRead)
                                (fun row : BHist =>
                                  UnaryHistory row ∧ Cont S A callRead ∧
                                    Cont callRead T transcriptRead ∧
                                      Cont transcriptRead B boundaryRead ∧
                                        Cont boundaryRead E evidenceRead ∧
                                          Cont evidenceRead N namedRead)
                                hsame ∧
                              UnaryHistory namedRead := by
  -- BEDC touchpoint anchor: BHist Cont hsame SemanticNameCert UnaryHistory
  intro sUnary aUnary tUnary bUnary eUnary _hUnary nUnary callRoute transcriptRoute
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
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row namedRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row S ∨ hsame row A ∨ hsame row T ∨ hsame row B ∨ hsame row E ∨
              hsame row H ∨ hsame row N ∨ hsame row callRead ∨ hsame row transcriptRead ∨
                hsame row boundaryRead ∨ hsame row evidenceRead ∨ hsame row namedRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont S A callRead ∧ Cont callRead T transcriptRead ∧
              Cont transcriptRead B boundaryRead ∧ Cont boundaryRead E evidenceRead ∧
                Cont evidenceRead N namedRead)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro namedRead ⟨hsame_refl namedRead, namedUnary⟩
      equiv_refl := by
        intro row _source
        exact hsame_refl row
      equiv_symm := by
        intro _row _other sameRows
        exact hsame_symm sameRows
      equiv_trans := by
        intro _row _middle _other sameLeft sameRight
        exact hsame_trans sameLeft sameRight
      carrier_respects_equiv := by
        intro _row _other sameRows source
        exact
          ⟨hsame_trans (hsame_symm sameRows) source.left,
            unary_transport source.right sameRows⟩
    }
    pattern_sound := by
      intro _row source
      exact
        Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <|
          Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr source.left
    ledger_sound := by
      intro _row source
      exact
        ⟨source.right, callRoute, transcriptRoute, boundaryRoute, evidenceRoute, nameRoute⟩
  }
  exact ⟨cert, namedUnary⟩

theorem OracleAugmentedSubstrateCarrier_classifier_transport
    {S A T B E H C P N callRead transcriptRead boundaryRead evidenceRead namedRead
      transportedRead : BHist} :
    UnaryHistory S →
      UnaryHistory A →
        UnaryHistory T →
          UnaryHistory B →
            UnaryHistory E →
              UnaryHistory H →
                UnaryHistory C →
                  UnaryHistory P →
                    UnaryHistory N →
                      Cont S A callRead →
                        Cont callRead T transcriptRead →
                          Cont transcriptRead B boundaryRead →
                            Cont boundaryRead E evidenceRead →
                              Cont evidenceRead P namedRead →
                                hsame namedRead transportedRead →
                                  SemanticNameCert
                                      (fun row : BHist =>
                                        hsame row transportedRead ∧ UnaryHistory row)
                                      (fun row : BHist =>
                                        hsame row S ∨ hsame row A ∨ hsame row T ∨
                                          hsame row B ∨ hsame row E ∨ hsame row C ∨
                                            hsame row P ∨ hsame row N ∨ hsame row callRead ∨
                                              hsame row transcriptRead ∨
                                                hsame row boundaryRead ∨
                                                  hsame row evidenceRead ∨
                                                    hsame row namedRead ∨
                                                      hsame row transportedRead)
                                      (fun row : BHist =>
                                        UnaryHistory row ∧ Cont S A callRead ∧
                                          Cont callRead T transcriptRead ∧
                                            Cont transcriptRead B boundaryRead ∧
                                              Cont boundaryRead E evidenceRead ∧
                                                Cont evidenceRead P namedRead)
                                      hsame ∧
                                    UnaryHistory transportedRead := by
  -- BEDC touchpoint anchor: BHist Cont hsame SemanticNameCert UnaryHistory
  intro sUnary aUnary tUnary bUnary eUnary _hUnary _cUnary pUnary _nUnary callRoute
    transcriptRoute boundaryRoute evidenceRoute nameRoute namedTransport
  have callUnary : UnaryHistory callRead :=
    unary_cont_closed sUnary aUnary callRoute
  have transcriptUnary : UnaryHistory transcriptRead :=
    unary_cont_closed callUnary tUnary transcriptRoute
  have boundaryUnary : UnaryHistory boundaryRead :=
    unary_cont_closed transcriptUnary bUnary boundaryRoute
  have evidenceUnary : UnaryHistory evidenceRead :=
    unary_cont_closed boundaryUnary eUnary evidenceRoute
  have namedUnary : UnaryHistory namedRead :=
    unary_cont_closed evidenceUnary pUnary nameRoute
  have transportedUnary : UnaryHistory transportedRead :=
    unary_transport namedUnary namedTransport
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row transportedRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row S ∨ hsame row A ∨ hsame row T ∨ hsame row B ∨ hsame row E ∨
              hsame row C ∨ hsame row P ∨ hsame row N ∨ hsame row callRead ∨
                hsame row transcriptRead ∨ hsame row boundaryRead ∨ hsame row evidenceRead ∨
                  hsame row namedRead ∨ hsame row transportedRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont S A callRead ∧ Cont callRead T transcriptRead ∧
              Cont transcriptRead B boundaryRead ∧ Cont boundaryRead E evidenceRead ∧
                Cont evidenceRead P namedRead)
          hsame := {
    core := {
      carrier_inhabited :=
        Exists.intro transportedRead ⟨hsame_refl transportedRead, transportedUnary⟩
      equiv_refl := by
        intro row _source
        exact hsame_refl row
      equiv_symm := by
        intro _row _other sameRows
        exact hsame_symm sameRows
      equiv_trans := by
        intro _row _middle _other sameLeft sameRight
        exact hsame_trans sameLeft sameRight
      carrier_respects_equiv := by
        intro _row _other sameRows source
        exact
          ⟨hsame_trans (hsame_symm sameRows) source.left,
            unary_transport source.right sameRows⟩
    }
    pattern_sound := by
      intro _row source
      exact
        Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <|
          Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr source.left
    ledger_sound := by
      intro _row source
      exact
        ⟨source.right, callRoute, transcriptRoute, boundaryRoute, evidenceRoute, nameRoute⟩
  }
  exact ⟨cert, transportedUnary⟩

theorem OracleAugmentedSubstrateCarrier_row_exposure [AskSetup] [PackageSetup]
    {S A T B E H C P N callRead transcriptRead boundaryRead evidenceRead packageRead
      namedRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    UnaryHistory S →
      UnaryHistory A →
        UnaryHistory T →
          UnaryHistory B →
            UnaryHistory E →
              UnaryHistory H →
                UnaryHistory C →
                  UnaryHistory P →
                    UnaryHistory N →
                      Cont S A callRead →
                        Cont callRead T transcriptRead →
                          Cont transcriptRead B boundaryRead →
                            Cont boundaryRead E evidenceRead →
                              Cont evidenceRead P packageRead →
                                Cont packageRead N namedRead →
                                  PkgSig bundle namedRead pkg →
                                    UnaryHistory S ∧ UnaryHistory A ∧ UnaryHistory T ∧
                                      UnaryHistory B ∧ UnaryHistory E ∧ UnaryHistory H ∧
                                        UnaryHistory C ∧ UnaryHistory P ∧ UnaryHistory N ∧
                                          UnaryHistory callRead ∧
                                            UnaryHistory transcriptRead ∧
                                              UnaryHistory boundaryRead ∧
                                                UnaryHistory evidenceRead ∧
                                                  UnaryHistory packageRead ∧
                                                    UnaryHistory namedRead ∧
                                                      Cont S A callRead ∧
                                                        Cont callRead T transcriptRead ∧
                                                          Cont transcriptRead B boundaryRead ∧
                                                            Cont boundaryRead E evidenceRead ∧
                                                              Cont evidenceRead P packageRead ∧
                                                                Cont packageRead N namedRead ∧
                                                                  PkgSig bundle namedRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont UnaryHistory PkgSig
  intro sUnary aUnary tUnary bUnary eUnary hUnary cUnary pUnary nUnary callRoute
    transcriptRoute boundaryRoute evidenceRoute packageRoute namedRoute namedPkg
  have callUnary : UnaryHistory callRead :=
    unary_cont_closed sUnary aUnary callRoute
  have transcriptUnary : UnaryHistory transcriptRead :=
    unary_cont_closed callUnary tUnary transcriptRoute
  have boundaryUnary : UnaryHistory boundaryRead :=
    unary_cont_closed transcriptUnary bUnary boundaryRoute
  have evidenceUnary : UnaryHistory evidenceRead :=
    unary_cont_closed boundaryUnary eUnary evidenceRoute
  have packageUnary : UnaryHistory packageRead :=
    unary_cont_closed evidenceUnary pUnary packageRoute
  have namedUnary : UnaryHistory namedRead :=
    unary_cont_closed packageUnary nUnary namedRoute
  exact
    ⟨sUnary, aUnary, tUnary, bUnary, eUnary, hUnary, cUnary, pUnary, nUnary,
      callUnary, transcriptUnary, boundaryUnary, evidenceUnary, packageUnary, namedUnary,
      callRoute, transcriptRoute, boundaryRoute, evidenceRoute, packageRoute, namedRoute,
      namedPkg⟩

end BEDC.Derived.OracleAugmentedSubstrateUp
