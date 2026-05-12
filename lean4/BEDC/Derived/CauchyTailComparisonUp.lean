import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.CauchyTailComparisonUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def CauchyTailComparisonCarrier [AskSetup] [PackageSetup]
    (leftName rightName modulus window endpointLedger readback provenance namecert endpoint :
      BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  UnaryHistory leftName ∧
    UnaryHistory rightName ∧
    UnaryHistory modulus ∧
    UnaryHistory window ∧
    UnaryHistory endpointLedger ∧
    UnaryHistory readback ∧
    UnaryHistory provenance ∧
    UnaryHistory namecert ∧
    UnaryHistory endpoint ∧
    Cont (append leftName rightName) modulus window ∧
    Cont window endpointLedger readback ∧
    hsame endpoint (append readback provenance) ∧
    hsame namecert endpoint ∧
    PkgSig bundle endpoint pkg

theorem CauchyTailComparisonCarrier_tail_stability [AskSetup] [PackageSetup]
    {leftName rightName modulus window endpointLedger readback provenance namecert endpoint :
      BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CauchyTailComparisonCarrier leftName rightName modulus window endpointLedger readback
      provenance namecert endpoint bundle pkg →
      Cont (append leftName rightName) modulus window ∧
        Cont window endpointLedger readback ∧
          hsame endpoint (append readback provenance) ∧ PkgSig bundle endpoint pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg hsame Cont
  intro carrier
  cases carrier with
  | intro _leftUnary rest =>
      cases rest with
      | intro _rightUnary rest =>
          cases rest with
          | intro _modulusUnary rest =>
              cases rest with
              | intro _windowUnary rest =>
                  cases rest with
                  | intro _endpointLedgerUnary rest =>
                      cases rest with
                      | intro _readbackUnary rest =>
                          cases rest with
                          | intro _provenanceUnary rest =>
                              cases rest with
                              | intro _namecertUnary rest =>
                                  cases rest with
                                  | intro _endpointUnary rest =>
                                      cases rest with
                                      | intro commonWindow rest =>
                                          cases rest with
                                          | intro endpointReadback rest =>
                                              cases rest with
                                              | intro endpointSame rest =>
                                                  cases rest with
                                                  | intro _namecertSame pkgSig =>
                                                      exact And.intro commonWindow
                                                        (And.intro endpointReadback
                                                          (And.intro endpointSame pkgSig))

theorem CauchyTailComparisonCarrier_real_completion_handoff [AskSetup] [PackageSetup]
    {leftName rightName modulus window endpointLedger readback provenance namecert endpoint :
      BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CauchyTailComparisonCarrier leftName rightName modulus window endpointLedger readback
        provenance namecert endpoint bundle pkg →
      UnaryHistory leftName ∧
        UnaryHistory rightName ∧
          UnaryHistory modulus ∧
            UnaryHistory window ∧
              UnaryHistory endpointLedger ∧
                UnaryHistory readback ∧
                  UnaryHistory provenance ∧
                    UnaryHistory namecert ∧
                      Cont (append leftName rightName) modulus window ∧
                        Cont window endpointLedger readback ∧
                          hsame endpoint (append readback provenance) ∧
                            hsame namecert endpoint ∧ PkgSig bundle endpoint pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg hsame Cont
  intro carrier
  obtain ⟨leftUnary, rightUnary, modulusUnary, windowUnary, endpointLedgerUnary,
    readbackUnary, provenanceUnary, namecertUnary, _endpointUnary, commonWindow,
    endpointReadback, endpointSame, namecertSame, pkgSig⟩ := carrier
  exact And.intro leftUnary
    (And.intro rightUnary
      (And.intro modulusUnary
        (And.intro windowUnary
          (And.intro endpointLedgerUnary
            (And.intro readbackUnary
              (And.intro provenanceUnary
                (And.intro namecertUnary
                  (And.intro commonWindow
                    (And.intro endpointReadback
                      (And.intro endpointSame
                        (And.intro namecertSame pkgSig)))))))))))

def CauchyTailComparisonCommonWindowCarrier [AskSetup] [PackageSetup]
    (leftName rightName modulus window endpointLedger readback provenance nameRow endpoint :
      BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  UnaryHistory leftName ∧ UnaryHistory rightName ∧ UnaryHistory modulus ∧
    UnaryHistory window ∧ UnaryHistory nameRow ∧ Cont modulus window endpointLedger ∧
      Cont endpointLedger readback endpoint ∧ hsame provenance (append leftName rightName) ∧
        PkgSig bundle endpoint pkg

theorem CauchyTailComparisonCommonWindowCarrier_semantic_name_certificate
    [AskSetup] [PackageSetup]
    {leftName rightName modulus window endpointLedger readback provenance nameRow endpoint :
      BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CauchyTailComparisonCommonWindowCarrier leftName rightName modulus window endpointLedger
        readback provenance nameRow endpoint bundle pkg ->
      SemanticNameCert
        (fun row : BHist =>
          CauchyTailComparisonCommonWindowCarrier leftName rightName modulus window
            endpointLedger readback provenance nameRow endpoint bundle pkg ∧ hsame row endpoint)
        (fun row : BHist =>
          CauchyTailComparisonCommonWindowCarrier leftName rightName modulus window
            endpointLedger readback provenance nameRow endpoint bundle pkg ∧ hsame row endpoint)
        (fun row : BHist =>
          CauchyTailComparisonCommonWindowCarrier leftName rightName modulus window
            endpointLedger readback provenance nameRow endpoint bundle pkg ∧ hsame row endpoint)
        hsame := by
  intro carrier
  have carrierSource := carrier
  obtain ⟨_leftUnary, _rightUnary, modulusUnary, windowUnary, _nameUnary,
    modulusWindowLedger, ledgerReadbackEndpoint, _provenanceRows, _endpointPkg⟩ := carrier
  have endpointLedgerUnary : UnaryHistory endpointLedger :=
    unary_cont_closed modulusUnary windowUnary modulusWindowLedger
  have _sameEndpointLedger : Cont endpointLedger readback endpoint := ledgerReadbackEndpoint
  have _endpointLedgerUnary : UnaryHistory endpointLedger := endpointLedgerUnary
  exact {
    core := {
      carrier_inhabited := Exists.intro endpoint (And.intro carrierSource (hsame_refl endpoint))
      equiv_refl := by
        intro row _source
        exact hsame_refl row
      equiv_symm := by
        intro _row _row' sameRows
        exact hsame_symm sameRows
      equiv_trans := by
        intro _row _row' _row'' sameLeft sameRight
        exact hsame_trans sameLeft sameRight
      carrier_respects_equiv := by
        intro _row _row' sameRows source
        cases sameRows
        exact source
    }
    pattern_sound := by
      intro _row source
      exact source
    ledger_sound := by
      intro _row source
      exact source
  }

end BEDC.Derived.CauchyTailComparisonUp
