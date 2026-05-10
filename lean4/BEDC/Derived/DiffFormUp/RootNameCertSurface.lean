import BEDC.Derived.DiffFormUp.RootConsumerFace
import BEDC.Derived.DiffFormUp.SemanticCertificate

namespace BEDC.Derived.DiffFormUp

open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Unary

theorem DiffFormRootNameCert_surface {ScalarCarrier : BHist -> Prop}
    {ScalarClassifier : BHist -> BHist -> Prop}
    (scalarCert : NameCert ScalarCarrier ScalarClassifier) {probes : ProbeBundle BHist}
    {degree probe tensor scalar antisym ledger dplus outDegree rightLedger tensorLedger :
      BHist} :
    InBundle probe probes -> ScalarCarrier scalar -> UnaryHistory degree -> UnaryHistory probe ->
      Cont degree probe tensor -> UnaryHistory antisym -> Cont tensor antisym scalar ->
        hsame ledger (append degree (append probe (append tensor (append scalar antisym)))) ->
          Cont degree (BHist.e1 BHist.Empty) dplus -> Cont degree dplus outDegree ->
            UnaryHistory rightLedger -> hsame ledger rightLedger -> UnaryHistory tensorLedger ->
              SemanticNameCert
                  (fun raised : BHist =>
                    DiffFormExteriorDerivativeLedger scalar raised degree raised probe probe
                      tensor tensor scalar scalar antisym ledger)
                  (fun raised : BHist =>
                    DiffFormExteriorDerivativeLedger scalar raised degree raised probe probe
                      tensor tensor scalar scalar antisym ledger)
                  (fun raised : BHist =>
                    DiffFormExteriorDerivativeLedger scalar raised degree raised probe probe
                      tensor tensor scalar scalar antisym ledger)
                  hsame ∧
                DiffFormWedgeDegreeLedger degree dplus outDegree ledger rightLedger tensorLedger ∧
                  DiffFormBHistClassifier ScalarClassifier probes degree probe tensor scalar antisym
                    ledger degree probe tensor scalar antisym ledger := by
  intro probeIn scalarCarrier degreeUnary probeUnary tensorRoute antisymUnary scalarRoute
    ledgerRoute degreeSuccessor wedgeRoute rightLedgerUnary sameRightLedger tensorLedgerUnary
  have routed :
      DiffFormBHistClassifier ScalarClassifier probes degree probe tensor scalar antisym ledger
          degree probe tensor scalar antisym ledger ∧
        DiffFormExteriorDerivativeLedger scalar dplus degree dplus probe probe tensor tensor
          scalar scalar antisym ledger ∧
          DiffFormWedgeDegreeLedger degree dplus outDegree ledger rightLedger tensorLedger :=
    DiffFormRootConsumerPackage_operation_routing scalarCert probeIn scalarCarrier degreeUnary
      probeUnary tensorRoute antisymUnary scalarRoute ledgerRoute degreeSuccessor wedgeRoute
      rightLedgerUnary sameRightLedger tensorLedgerUnary
  have cert :
      SemanticNameCert
          (fun raised : BHist =>
            DiffFormExteriorDerivativeLedger scalar raised degree raised probe probe tensor tensor
              scalar scalar antisym ledger)
          (fun raised : BHist =>
            DiffFormExteriorDerivativeLedger scalar raised degree raised probe probe tensor tensor
              scalar scalar antisym ledger)
          (fun raised : BHist =>
            DiffFormExteriorDerivativeLedger scalar raised degree raised probe probe tensor tensor
              scalar scalar antisym ledger)
          hsame :=
    {
      core := {
        carrier_inhabited := Exists.intro dplus routed.right.left
        equiv_refl := by
          intro raised _source
          exact hsame_refl raised
        equiv_symm := by
          intro _raised _raised' sameRaised
          exact hsame_symm sameRaised
        equiv_trans := by
          intro _raised _raised' _raised'' sameLeft sameRight
          exact hsame_trans sameLeft sameRight
        carrier_respects_equiv := by
          intro raised raised' sameRaised sourceLedger
          exact
            (DiffFormExteriorDerivativeLedger_hsame_transport_degree_raise
              (hsame_refl scalar) sameRaised (hsame_refl degree) sameRaised
              (hsame_refl probe) (hsame_refl probe) (hsame_refl tensor) (hsame_refl tensor)
              (hsame_refl scalar) (hsame_refl scalar) (hsame_refl antisym)
              (hsame_refl ledger) sourceLedger).left
      }
      pattern_sound := by
        intro _raised source
        exact source
      ledger_sound := by
        intro _raised source
        exact source
    }
  exact And.intro cert (And.intro routed.right.right routed.left)

theorem DiffFormRootSource_transport_obligation {ScalarCarrier : BHist -> Prop}
    {ScalarClassifier : BHist -> BHist -> Prop}
    (scalarCert : NameCert ScalarCarrier ScalarClassifier) {probes : ProbeBundle BHist}
    {degree probe tensor scalar antisym ledger degree' probe' tensor' scalar' antisym'
      ledger' : BHist} :
    hsame degree degree' -> hsame probe probe' -> hsame tensor tensor' ->
      hsame scalar scalar' -> hsame antisym antisym' -> hsame ledger ledger' ->
        UnaryHistory degree -> UnaryHistory probe -> Cont degree probe tensor ->
          UnaryHistory antisym -> Cont tensor antisym scalar ->
            hsame ledger (append degree (append probe (append tensor (append scalar antisym)))) ->
              InBundle probe probes -> InBundle probe' probes -> ScalarCarrier scalar ->
                ScalarClassifier scalar scalar' ->
                  UnaryHistory degree' ∧ UnaryHistory probe' ∧ UnaryHistory tensor' ∧
                    UnaryHistory scalar' ∧
                      DiffFormBHistClassifier ScalarClassifier probes degree probe tensor scalar
                        antisym ledger degree' probe' tensor' scalar' antisym' ledger' := by
  intro sameDegree sameProbe sameTensor sameScalar sameAntisym sameLedger degreeUnary
    probeUnary tensorRoute antisymUnary scalarRoute ledgerRoute probeIn probeIn' scalarCarrier
    scalarClassified
  have transported :
      UnaryHistory degree' ∧ UnaryHistory probe' ∧ UnaryHistory tensor' ∧
        UnaryHistory scalar' ∧
          hsame ledger'
            (append degree' (append probe' (append tensor' (append scalar' antisym')))) :=
    DiffFormBHistCarrier_hsame_transport sameDegree sameProbe sameTensor sameScalar sameAntisym
      sameLedger degreeUnary probeUnary tensorRoute antisymUnary scalarRoute ledgerRoute
  have classifierBase :
      DiffFormBHistClassifier ScalarClassifier probes degree probe tensor scalar antisym ledger
        degree probe tensor scalar antisym ledger :=
    DiffFormBHistClassifier_reflexivity_obligation scalarCert probeIn scalarCarrier
  have classifierRows :
      DiffFormBHistClassifier ScalarClassifier probes degree probe tensor scalar antisym ledger
        degree' probe' tensor' scalar' antisym' ledger' :=
    DiffFormBHistClassifier_hsame_component_stability scalarCert probeIn probeIn'
      (hsame_refl degree) (hsame_refl probe) (hsame_refl tensor)
      (NameCert.equiv_refl scalarCert scalarCarrier) (hsame_refl antisym) (hsame_refl ledger)
      classifierBase sameDegree sameProbe sameTensor scalarClassified sameAntisym sameLedger
  exact And.intro transported.left
    (And.intro transported.right.left
      (And.intro transported.right.right.left
        (And.intro transported.right.right.right.left classifierRows)))

end BEDC.Derived.DiffFormUp
