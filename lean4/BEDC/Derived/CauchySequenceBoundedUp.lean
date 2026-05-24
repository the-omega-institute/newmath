import BEDC.Derived.CauchySequenceBoundedUp.TasteGate

namespace BEDC.Derived.CauchySequenceBoundedUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem CauchySequenceBoundedCarrier_dyadic_bound_stability [AskSetup] [PackageSetup]
    {schedule modulus tolerance readback realSeal bound transport route provenance name
      transportedBound : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CauchySequenceBoundedCarrier schedule modulus tolerance readback realSeal bound transport
        route provenance name bundle pkg ->
      hsame bound transportedBound ->
        PkgSig bundle transportedBound pkg ->
          UnaryHistory schedule ∧ UnaryHistory modulus ∧ UnaryHistory tolerance ∧
            UnaryHistory transportedBound ∧ hsame bound transportedBound ∧
              PkgSig bundle name pkg ∧ PkgSig bundle transportedBound pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg hsame UnaryHistory PkgSig
  intro carrier boundSame transportedBoundPkg
  obtain ⟨scheduleUnary, modulusUnary, toleranceUnary, boundUnary, _routeUnary,
    _provenanceUnary, _scheduleModulusTolerance, _toleranceBoundReadback,
    _readbackRouteSeal, _provenanceTransportName, namePkg⟩ := carrier
  have transportedBoundUnary : UnaryHistory transportedBound :=
    unary_transport boundUnary boundSame
  exact
    ⟨scheduleUnary, modulusUnary, toleranceUnary, transportedBoundUnary, boundSame, namePkg,
      transportedBoundPkg⟩

end BEDC.Derived.CauchySequenceBoundedUp
