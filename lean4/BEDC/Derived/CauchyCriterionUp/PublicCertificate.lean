import BEDC.Derived.CauchyCriterionUp

namespace BEDC.Derived.CauchyCriterionUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Sig
open BEDC.FKernel.Unary

theorem CauchyCriterionCarrier_public_certificate [AskSetup] [PackageSetup]
    {window modulus tolerance ledger regseq realSeal transport route provenance localCert endpoint
      publicRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CauchyCriterionCarrier window modulus tolerance ledger regseq realSeal transport route
        provenance localCert endpoint bundle pkg ->
      Cont endpoint localCert publicRead ->
        PkgSig bundle publicRead pkg ->
          SemanticNameCert
            (fun row : BHist =>
              CauchyCriterionCarrier window modulus tolerance ledger regseq realSeal transport route
                  provenance localCert endpoint bundle pkg ∧ hsame row publicRead)
            (fun row : BHist =>
              Cont window modulus tolerance ∧ Cont tolerance ledger regseq ∧
                Cont regseq realSeal transport ∧ Cont endpoint localCert row)
            (fun row : BHist =>
              UnaryHistory row ∧ PkgSig bundle publicRead pkg ∧ PkgSig bundle endpoint pkg)
            hsame := by
  -- BEDC touchpoint anchor: BHist Cont PkgSig SemanticNameCert hsame
  intro carrier endpointLocalCertPublicRead publicPkg
  have carrierSource :
      CauchyCriterionCarrier window modulus tolerance ledger regseq realSeal transport route
        provenance localCert endpoint bundle pkg :=
    carrier
  obtain ⟨_windowUnary, _modulusUnary, _toleranceUnary, _ledgerUnary, _regseqUnary,
    _realSealUnary, _transportUnary, _routeUnary, _provenanceUnary, localCertUnary,
    endpointUnary, windowModulusTolerance, toleranceLedgerRegseq, regseqRealSealTransport,
    _transportLocalCertRoute, _routeProvenanceEndpoint, endpointPkg⟩ := carrier
  have publicUnary : UnaryHistory publicRead :=
    unary_cont_closed endpointUnary localCertUnary endpointLocalCertPublicRead
  exact {
    core := {
      carrier_inhabited :=
        Exists.intro publicRead (And.intro carrierSource (hsame_refl publicRead))
      equiv_refl := by
        intro row _source
        exact hsame_refl row
      equiv_symm := by
        intro row row' sameRows
        exact hsame_symm sameRows
      equiv_trans := by
        intro row row' row'' sameLeft sameRight
        exact hsame_trans sameLeft sameRight
      carrier_respects_equiv := by
        intro row row' sameRows source
        exact And.intro source.left (hsame_trans (hsame_symm sameRows) source.right)
    }
    pattern_sound := by
      intro row source
      have endpointLocalCertRow : Cont endpoint localCert row :=
        cont_result_hsame_transport endpointLocalCertPublicRead (hsame_symm source.right)
      exact
        ⟨windowModulusTolerance, toleranceLedgerRegseq, regseqRealSealTransport,
          endpointLocalCertRow⟩
    ledger_sound := by
      intro row source
      have rowUnary : UnaryHistory row :=
        unary_transport publicUnary (hsame_symm source.right)
      exact ⟨rowUnary, publicPkg, endpointPkg⟩
  }

end BEDC.Derived.CauchyCriterionUp
