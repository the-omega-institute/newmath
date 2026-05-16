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

theorem CauchyCriterionCarrier_real_completion_consumer_bridge [AskSetup] [PackageSetup]
    {window modulus tolerance ledger regseq realSeal transport route provenance localCert endpoint
      completionRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CauchyCriterionCarrier window modulus tolerance ledger regseq realSeal transport route
        provenance localCert endpoint bundle pkg ->
      Cont endpoint realSeal completionRead ->
        PkgSig bundle completionRead pkg ->
          SemanticNameCert
            (fun row : BHist =>
              CauchyCriterionCarrier window modulus tolerance ledger regseq realSeal transport route
                  provenance localCert endpoint bundle pkg ∧ hsame row completionRead)
            (fun row : BHist =>
              Cont window modulus tolerance ∧ Cont tolerance ledger regseq ∧
                Cont route provenance endpoint ∧ Cont endpoint realSeal row)
            (fun row : BHist =>
              UnaryHistory row ∧ PkgSig bundle endpoint pkg ∧ PkgSig bundle completionRead pkg)
            hsame := by
  -- BEDC touchpoint anchor: BHist Cont PkgSig SemanticNameCert hsame
  intro carrier endpointRealSealCompletion completionPkg
  have carrierSource :
      CauchyCriterionCarrier window modulus tolerance ledger regseq realSeal transport route
        provenance localCert endpoint bundle pkg :=
    carrier
  obtain ⟨_windowUnary, _modulusUnary, _toleranceUnary, _ledgerUnary, _regseqUnary,
    realSealUnary, _transportUnary, _routeUnary, _provenanceUnary, _localCertUnary,
    endpointUnary, windowModulusTolerance, toleranceLedgerRegseq, _regseqRealSealTransport,
    _transportLocalCertRoute, routeProvenanceEndpoint, endpointPkg⟩ := carrier
  have completionUnary : UnaryHistory completionRead :=
    unary_cont_closed endpointUnary realSealUnary endpointRealSealCompletion
  exact {
    core := {
      carrier_inhabited :=
        Exists.intro completionRead (And.intro carrierSource (hsame_refl completionRead))
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
      have endpointRealSealRow : Cont endpoint realSeal row :=
        cont_result_hsame_transport endpointRealSealCompletion (hsame_symm source.right)
      exact
        ⟨windowModulusTolerance, toleranceLedgerRegseq, routeProvenanceEndpoint,
          endpointRealSealRow⟩
    ledger_sound := by
      intro row source
      have rowUnary : UnaryHistory row :=
        unary_transport completionUnary (hsame_symm source.right)
      exact ⟨rowUnary, endpointPkg, completionPkg⟩
  }

end BEDC.Derived.CauchyCriterionUp
