import BEDC.Derived.StackUp

namespace BEDC.Derived.StackUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Sig
open BEDC.FKernel.Unary
open BEDC.Derived.CommRingUp
open BEDC.Derived.RingedSpaceUp
open BEDC.Derived.SchemeUp

theorem StackRepresentability_scheme_site_transport [AskSetup] [PackageSetup]
    {point openHist sectionHist germ ringEndpoint chartA chartB overlap tail site objectRows
      arrowRows transportRows restrictionRows descentRows representabilityRows provenance ledger
      endpoint : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    SchemeSingletonPackage point openHist sectionHist germ ringEndpoint chartA chartB overlap ->
      StackCarrierPacket site objectRows arrowRows transportRows restrictionRows descentRows
          representabilityRows provenance ledger endpoint bundle pkg ->
        hsame site ringEndpoint ->
          UnaryHistory site ∧ RingedSpaceSingletonSurface point openHist sectionHist germ ringEndpoint ∧
            CommRingSingletonCarrier chartA ∧ CommRingSingletonCarrier chartB ∧
              PkgSig bundle endpoint pkg ∧ (hsame overlap (BHist.e0 tail) -> False) := by
  intro schemePackage packet _sameSite
  have schemeRows :=
    SchemeSingletonPackage_carrier_source_obligation (tail := tail) schemePackage
  obtain ⟨siteUnary, _objectUnary, _arrowUnary, _transportUnary, _restrictionUnary,
    _descentUnary, _representabilityUnary, _provenanceUnary, _ledgerUnary, _endpointUnary,
    _ledgerCont, _endpointCont, pkgSig⟩ := packet
  exact And.intro siteUnary
    (And.intro schemeRows.left
      (And.intro schemeRows.right.left
        (And.intro schemeRows.right.right.left
          (And.intro pkgSig schemeRows.right.right.right.right))))

end BEDC.Derived.StackUp
