import BEDC.Derived.ClosedboundedintervalUp

namespace BEDC.Derived.ClosedboundedintervalUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem ClosedBoundedIntervalPacket_endpoint_order_transport [AskSetup] [PackageSetup]
    {lower upper order rational dyadic stream readback sealRow transport replay provenance
      localName exported transportedOrder transportedDyadic : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ClosedBoundedIntervalPacket lower upper order rational dyadic stream readback sealRow
        transport replay provenance localName exported bundle pkg ->
      hsame order transportedOrder ->
        Cont transportedOrder rational transportedDyadic ->
          PkgSig bundle transportedDyadic pkg ->
            hsame order (append lower upper) ∧ UnaryHistory transportedOrder ∧
              UnaryHistory transportedDyadic ∧ Cont transportedOrder rational transportedDyadic ∧
                PkgSig bundle provenance pkg ∧ PkgSig bundle transportedDyadic pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg hsame Cont UnaryHistory PkgSig
  intro packet sameOrder transportedRoute transportedPkg
  obtain ⟨lowerUnary, upperUnary, orderUnary, rationalUnary, _dyadicUnary, _streamUnary,
    _readbackUnary, _sealRowUnary, _transportUnary, _replayUnary, _provenanceUnary,
    _localNameUnary, _exportedUnary, endpointRoute, _containmentRoute, _sealRoute,
    _replayRoute, _nameRoute, provenancePkg, _localNamePkg⟩ := packet
  have transportedOrderUnary : UnaryHistory transportedOrder :=
    unary_transport orderUnary sameOrder
  have transportedDyadicUnary : UnaryHistory transportedDyadic :=
    unary_cont_closed transportedOrderUnary rationalUnary transportedRoute
  exact
    ⟨endpointRoute, transportedOrderUnary, transportedDyadicUnary, transportedRoute,
      provenancePkg, transportedPkg⟩

end BEDC.Derived.ClosedboundedintervalUp
