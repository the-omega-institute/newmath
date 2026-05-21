import BEDC.Derived.RegularCauchyNameUp

namespace BEDC.Derived.RegularCauchyNameUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem RegularCauchyNameCarrier_window_radius_seal_scoped_package [AskSetup]
    [PackageSetup]
    {schedule observation radius ledger sealRow provenance namecert endpoint window readback
      endpointRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    RegularCauchyNameCarrier schedule observation radius ledger sealRow provenance namecert
        endpoint bundle pkg ->
      Cont schedule observation window ->
        Cont window radius readback ->
          Cont sealRow provenance endpointRead ->
            PkgSig bundle readback pkg ->
              PkgSig bundle endpointRead pkg ->
                UnaryHistory schedule ∧ UnaryHistory window ∧ UnaryHistory radius ∧
                  UnaryHistory readback ∧ hsame radius window ∧ hsame endpoint endpointRead ∧
                    PkgSig bundle endpoint pkg ∧ PkgSig bundle readback pkg ∧
                      PkgSig bundle endpointRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg hsame Cont
  intro carrier scheduleObservationWindow windowRadiusReadback sealProvenanceEndpointRead
    readbackPkg endpointReadPkg
  have finiteReadback :=
    RegularCauchyNameCarrier_finite_window_readback_exactness carrier
      scheduleObservationWindow windowRadiusReadback readbackPkg
  obtain ⟨_scheduleUnary, _observationUnary, _radiusUnary, _ledgerUnary, _sealUnary,
    _provenanceUnary, _namecertUnary, _scheduleObservationRadius, _radiusLedgerSeal,
    sealProvenanceEndpoint, _endpointPkg⟩ := carrier
  have endpointSame : hsame endpoint endpointRead :=
    cont_deterministic sealProvenanceEndpoint sealProvenanceEndpointRead
  exact
    ⟨finiteReadback.left, finiteReadback.right.left, finiteReadback.right.right.left,
      finiteReadback.right.right.right.left, finiteReadback.right.right.right.right.left,
      endpointSame, finiteReadback.right.right.right.right.right.right.right.left,
      finiteReadback.right.right.right.right.right.right.right.right,
      endpointReadPkg⟩

end BEDC.Derived.RegularCauchyNameUp
