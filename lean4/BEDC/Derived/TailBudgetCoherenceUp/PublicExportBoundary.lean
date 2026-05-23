import BEDC.Derived.TailBudgetCoherenceUp

namespace BEDC.Derived.TailBudgetCoherenceUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem TailBudgetCoherenceCarrier_public_export_boundary [AskSetup] [PackageSetup]
    {meet observationBudget selectorBudget agreementSeal limitSeal window readback dyadic
      transport routes provenance localCert endpoint publicRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    TailBudgetCoherenceCarrier meet observationBudget selectorBudget agreementSeal limitSeal
        window readback dyadic transport routes provenance localCert endpoint bundle pkg ->
      Cont endpoint routes publicRead ->
        PkgSig bundle publicRead pkg ->
          SemanticNameCert
              (fun row : BHist =>
                TailBudgetCoherenceCarrier meet observationBudget selectorBudget agreementSeal
                    limitSeal window readback dyadic transport routes provenance localCert
                    endpoint bundle pkg ∧
                  hsame row publicRead)
              (fun row : BHist =>
                hsame row endpoint ∨ hsame row publicRead ∨ Cont endpoint routes row)
              (fun row : BHist => hsame row publicRead ∧ PkgSig bundle publicRead pkg)
              hsame ∧
            UnaryHistory publicRead := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame SemanticNameCert UnaryHistory
  intro carrier endpointRoutesPublic publicPkg
  have sourceCarrier := carrier
  obtain ⟨_meetUnary, _observationBudgetUnary, _selectorBudgetUnary, _agreementSealUnary,
    _limitSealUnary, _windowUnary, _readbackUnary, _dyadicUnary, _transportUnary,
    routesUnary, _provenanceUnary, _localCertUnary, endpointUnary, _meetObservationWindow,
    _meetSelectorDyadic, _windowDyadicReadback, _readbackAgreementLimit,
    _limitTransportRoutes, _routesProvenanceLocal, _provenanceLocalEndpoint,
    _sameEndpoint, _endpointPkg⟩ := carrier
  have publicUnary : UnaryHistory publicRead :=
    unary_cont_closed endpointUnary routesUnary endpointRoutesPublic
  have cert :
      SemanticNameCert
          (fun row : BHist =>
            TailBudgetCoherenceCarrier meet observationBudget selectorBudget agreementSeal
                limitSeal window readback dyadic transport routes provenance localCert endpoint
                bundle pkg ∧
              hsame row publicRead)
          (fun row : BHist =>
            hsame row endpoint ∨ hsame row publicRead ∨ Cont endpoint routes row)
          (fun row : BHist => hsame row publicRead ∧ PkgSig bundle publicRead pkg)
          hsame := by
    exact {
      core := {
        carrier_inhabited :=
          Exists.intro publicRead (And.intro sourceCarrier (hsame_refl publicRead))
        equiv_refl := by
          intro row _source
          exact hsame_refl row
        equiv_symm := by
          intro _row _row' same
          exact hsame_symm same
        equiv_trans := by
          intro _row _row' _row'' sameLeft sameRight
          exact hsame_trans sameLeft sameRight
        carrier_respects_equiv := by
          intro _row _row' same source
          exact And.intro source.left (hsame_trans (hsame_symm same) source.right)
      }
      pattern_sound := by
        intro _row source
        exact Or.inr (Or.inl source.right)
      ledger_sound := by
        intro _row source
        exact And.intro source.right publicPkg
    }
  exact And.intro cert publicUnary

end BEDC.Derived.TailBudgetCoherenceUp
