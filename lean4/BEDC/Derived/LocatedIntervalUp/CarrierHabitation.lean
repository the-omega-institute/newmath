import BEDC.Derived.LocatedIntervalUp

namespace BEDC.Derived.LocatedIntervalUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem LocatedIntervalPacket_carrier_habitation [AskSetup] [PackageSetup]
    {lower upper rationalCells dyadicRefinements streamWindows readbacks seals transport routes
      provenance nameCert endpoint : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    LocatedIntervalPacket lower upper rationalCells dyadicRefinements streamWindows readbacks seals
        transport routes provenance nameCert endpoint bundle pkg ->
      ∃ row : BHist,
        hsame row endpoint ∧ UnaryHistory row ∧ Cont lower upper rationalCells ∧
          Cont rationalCells dyadicRefinements endpoint ∧ PkgSig bundle endpoint pkg := by
  -- BEDC touchpoint anchor: BHist hsame Cont PkgSig UnaryHistory LocatedIntervalPacket
  intro packet
  obtain ⟨_lowerUnary, _upperUnary, rationalCellsUnary, dyadicUnary, _streamWindowsUnary,
    _readbacksUnary, _sealsUnary, _nameCertUnary, rationalCellsRoute, endpointRoute,
    _transportRoute, _routesRoute, _provenanceRoute, endpointPkg⟩ := packet
  have endpointUnary : UnaryHistory endpoint :=
    unary_cont_closed rationalCellsUnary dyadicUnary endpointRoute
  exact
    ⟨endpoint, hsame_refl endpoint, endpointUnary, rationalCellsRoute, endpointRoute,
      endpointPkg⟩

end BEDC.Derived.LocatedIntervalUp
