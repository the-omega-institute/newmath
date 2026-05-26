import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.SobolevUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def SobolevCarrier [AskSetup] [PackageSetup]
    (domain base codomain magnitude gradient transports routes provenance localCert : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  UnaryHistory domain ∧ UnaryHistory base ∧ UnaryHistory codomain ∧
    UnaryHistory magnitude ∧ UnaryHistory gradient ∧ UnaryHistory transports ∧
      UnaryHistory routes ∧ UnaryHistory provenance ∧ UnaryHistory localCert ∧
        Cont domain base codomain ∧ Cont codomain magnitude gradient ∧
          Cont gradient transports routes ∧ Cont routes provenance localCert ∧
            PkgSig bundle provenance pkg

theorem SobolevCarrier_namecert_obligation_surface [AskSetup] [PackageSetup]
    {domain base codomain magnitude gradient transports routes provenance localCert : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    SobolevCarrier domain base codomain magnitude gradient transports routes provenance
        localCert bundle pkg ->
      SemanticNameCert
          (fun row : BHist =>
            hsame row gradient ∧
              SobolevCarrier domain base codomain magnitude gradient transports routes provenance
                localCert bundle pkg)
          (fun row : BHist => hsame row gradient ∧ Cont codomain magnitude gradient)
          (fun row : BHist => hsame row gradient ∧ PkgSig bundle provenance pkg)
          hsame ∧
        UnaryHistory domain ∧ UnaryHistory base ∧ UnaryHistory codomain ∧
          UnaryHistory magnitude ∧ UnaryHistory gradient ∧ Cont domain base codomain ∧
            Cont codomain magnitude gradient ∧ PkgSig bundle provenance pkg := by
  intro carrier
  have carrierWitness := carrier
  obtain ⟨domainUnary, baseUnary, codomainUnary, magnitudeUnary, gradientUnary,
    _transportsUnary, _routesUnary, _provenanceUnary, _localCertUnary, domainBaseCodomain,
    codomainMagnitudeGradient, _gradientTransportRoutes, _routesProvenanceLocalCert,
    provenancePkg⟩ := carrier
  have sourceGradient :
      (fun row : BHist =>
        hsame row gradient ∧
          SobolevCarrier domain base codomain magnitude gradient transports routes provenance
            localCert bundle pkg) gradient := by
    exact ⟨hsame_refl gradient, carrierWitness⟩
  have core :
      NameCert
        (fun row : BHist =>
          hsame row gradient ∧
            SobolevCarrier domain base codomain magnitude gradient transports routes provenance
              localCert bundle pkg)
        hsame := {
    carrier_inhabited := Exists.intro gradient sourceGradient
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
      exact ⟨hsame_trans (hsame_symm sameRows) source.left, source.right⟩
  }
  have cert :
      SemanticNameCert
          (fun row : BHist =>
            hsame row gradient ∧
              SobolevCarrier domain base codomain magnitude gradient transports routes provenance
                localCert bundle pkg)
          (fun row : BHist => hsame row gradient ∧ Cont codomain magnitude gradient)
          (fun row : BHist => hsame row gradient ∧ PkgSig bundle provenance pkg)
          hsame := {
    core := core
    pattern_sound := by
      intro _row source
      exact ⟨source.left, codomainMagnitudeGradient⟩
    ledger_sound := by
      intro _row source
      exact ⟨source.left, provenancePkg⟩
  }
  exact
    ⟨cert, domainUnary, baseUnary, codomainUnary, magnitudeUnary, gradientUnary,
      domainBaseCodomain, codomainMagnitudeGradient, provenancePkg⟩

theorem SobolevCarrier_weak_derivative_ledger [AskSetup] [PackageSetup]
    {domain base codomain magnitude gradient transports routes provenance localCert : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    SobolevCarrier domain base codomain magnitude gradient transports routes provenance
        localCert bundle pkg ->
      exists derivativeRead : BHist,
        UnaryHistory derivativeRead ∧ hsame derivativeRead (append domain gradient) ∧
          Cont domain base codomain ∧ Cont codomain magnitude gradient ∧
            PkgSig bundle provenance pkg := by
  intro carrier
  obtain ⟨domainUnary, _baseUnary, _codomainUnary, _magnitudeUnary, gradientUnary,
    _transportsUnary, _routesUnary, _provenanceUnary, _localCertUnary, domainBaseCodomain,
    codomainMagnitudeGradient, _gradientTransportRoutes, _routesProvenanceLocalCert,
    provenancePkg⟩ := carrier
  exact
    ⟨append domain gradient, unary_append_closed domainUnary gradientUnary, hsame_refl _,
      domainBaseCodomain, codomainMagnitudeGradient, provenancePkg⟩

theorem SobolevCarrier_completion_boundary [AskSetup] [PackageSetup]
    {domain base codomain magnitude gradient transports routes provenance localCert : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    SobolevCarrier domain base codomain magnitude gradient transports routes provenance
        localCert bundle pkg ->
      exists publicRead : BHist,
        UnaryHistory publicRead ∧ hsame publicRead (append (append domain gradient) provenance) ∧
          Cont domain base codomain ∧ Cont codomain magnitude gradient ∧
            Cont gradient transports routes ∧ Cont routes provenance localCert ∧
              PkgSig bundle provenance pkg := by
  intro carrier
  obtain ⟨domainUnary, _baseUnary, _codomainUnary, _magnitudeUnary, gradientUnary,
    _transportsUnary, _routesUnary, provenanceUnary, _localCertUnary, domainBaseCodomain,
    codomainMagnitudeGradient, gradientTransportsRoutes, routesProvenanceLocalCert,
    provenancePkg⟩ := carrier
  have domainGradientUnary : UnaryHistory (append domain gradient) :=
    unary_append_closed domainUnary gradientUnary
  exact
    ⟨append (append domain gradient) provenance,
      unary_append_closed domainGradientUnary provenanceUnary, hsame_refl _, domainBaseCodomain,
      codomainMagnitudeGradient, gradientTransportsRoutes, routesProvenanceLocalCert,
      provenancePkg⟩

theorem SobolevCarrier_integral_derivative_source_package [AskSetup] [PackageSetup]
    {domain base codomain magnitude gradient transports routes provenance localCert : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    SobolevCarrier domain base codomain magnitude gradient transports routes provenance
        localCert bundle pkg ->
      exists analyticRoute : BHist,
        UnaryHistory analyticRoute ∧ hsame analyticRoute (append (append domain magnitude) gradient) ∧
          Cont domain base codomain ∧ Cont codomain magnitude gradient ∧
            Cont gradient transports routes ∧ PkgSig bundle provenance pkg := by
  intro carrier
  obtain ⟨domainUnary, _baseUnary, _codomainUnary, magnitudeUnary, gradientUnary,
    _transportsUnary, _routesUnary, _provenanceUnary, _localCertUnary, domainBaseCodomain,
    codomainMagnitudeGradient, gradientTransportsRoutes, _routesProvenanceLocalCert,
    provenancePkg⟩ := carrier
  have domainMagnitudeUnary : UnaryHistory (append domain magnitude) :=
    unary_append_closed domainUnary magnitudeUnary
  exact
    ⟨append (append domain magnitude) gradient,
      unary_append_closed domainMagnitudeUnary gradientUnary, hsame_refl _, domainBaseCodomain,
      codomainMagnitudeGradient, gradientTransportsRoutes, provenancePkg⟩

theorem SobolevCarrier_weak_derivative_carrier_transport [AskSetup] [PackageSetup]
    {domain base codomain magnitude gradient transports routes provenance localCert
      domain' base' codomain' magnitude' gradient' transports' routes' provenance' localCert' :
        BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    SobolevCarrier domain base codomain magnitude gradient transports routes provenance
        localCert bundle pkg ->
      SobolevCarrier domain' base' codomain' magnitude' gradient' transports' routes'
        provenance' localCert' bundle pkg ->
        hsame domain domain' ->
          hsame magnitude magnitude' ->
            hsame gradient gradient' ->
              exists sourceRead : BHist, exists targetRead : BHist,
                UnaryHistory sourceRead ∧ UnaryHistory targetRead ∧ hsame sourceRead targetRead ∧
                  hsame sourceRead (append (append domain magnitude) gradient) ∧
                    hsame targetRead (append (append domain' magnitude') gradient') ∧
                      Cont domain base codomain ∧ Cont codomain magnitude gradient ∧
                        Cont domain' base' codomain' ∧
                          Cont codomain' magnitude' gradient' ∧
                            PkgSig bundle provenance pkg ∧ PkgSig bundle provenance' pkg := by
  -- BEDC touchpoint anchor: BHist hsame Cont ProbeBundle Pkg UnaryHistory
  intro carrier carrier' sameDomain sameMagnitude sameGradient
  obtain ⟨domainUnary, _baseUnary, _codomainUnary, magnitudeUnary, gradientUnary,
    _transportsUnary, _routesUnary, _provenanceUnary, _localCertUnary, domainBaseCodomain,
    codomainMagnitudeGradient, _gradientTransportsRoutes, _routesProvenanceLocalCert,
    provenancePkg⟩ := carrier
  obtain ⟨domainUnary', _baseUnary', _codomainUnary', magnitudeUnary', gradientUnary',
    _transportsUnary', _routesUnary', _provenanceUnary', _localCertUnary',
    domainBaseCodomain', codomainMagnitudeGradient', _gradientTransportsRoutes',
    _routesProvenanceLocalCert', provenancePkg'⟩ := carrier'
  let sourceRead := append (append domain magnitude) gradient
  let targetRead := append (append domain' magnitude') gradient'
  have domainMagnitudeUnary : UnaryHistory (append domain magnitude) :=
    unary_append_closed domainUnary magnitudeUnary
  have domainMagnitudeUnary' : UnaryHistory (append domain' magnitude') :=
    unary_append_closed domainUnary' magnitudeUnary'
  have sourceUnary : UnaryHistory sourceRead :=
    unary_append_closed domainMagnitudeUnary gradientUnary
  have targetUnary : UnaryHistory targetRead :=
    unary_append_closed domainMagnitudeUnary' gradientUnary'
  cases sameDomain
  cases sameMagnitude
  cases sameGradient
  exact
    ⟨sourceRead, targetRead, sourceUnary, targetUnary, hsame_refl sourceRead,
      hsame_refl sourceRead, hsame_refl targetRead, domainBaseCodomain,
      codomainMagnitudeGradient, domainBaseCodomain', codomainMagnitudeGradient',
      provenancePkg, provenancePkg'⟩

end BEDC.Derived.SobolevUp
