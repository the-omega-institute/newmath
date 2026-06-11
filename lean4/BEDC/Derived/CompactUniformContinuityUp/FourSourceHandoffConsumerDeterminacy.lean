import BEDC.Derived.CompactUniformContinuityUp

namespace BEDC.Derived.CompactUniformContinuityUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem CompactUniformContinuityPacket_four_source_handoff_consumer_determinacy
    [AskSetup] [PackageSetup]
    {source target graph tolerance precision net coverage modulusRows radiusRows fold transport
      route nameRow firstSource secondSource : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CompactUniformContinuityPacket source target graph tolerance precision net coverage
        modulusRows radiusRows fold transport route nameRow bundle pkg ->
      Cont net coverage firstSource ->
        Cont net coverage secondSource ->
          PkgSig bundle precision pkg ->
            hsame firstSource secondSource ∧ UnaryHistory firstSource ∧
              UnaryHistory secondSource ∧ PkgSig bundle precision pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig hsame UnaryHistory
  intro packet firstRoute secondRoute precisionPkg
  obtain ⟨_sourceUnary, _targetUnary, _graphUnary, _toleranceUnary, netUnary,
    coverageUnary, _radiusRowsUnary, _transportUnary, _nameRowUnary,
    _netCoverageModulusRows, _modulusRowsRadiusRowsFold, _foldTransportRoute,
    _routeNamePrecision, _packetPrecisionPkg⟩ := packet
  have sameSources : hsame firstSource secondSource :=
    cont_deterministic firstRoute secondRoute
  have firstUnary : UnaryHistory firstSource :=
    unary_cont_closed netUnary coverageUnary firstRoute
  have secondUnary : UnaryHistory secondSource :=
    unary_cont_closed netUnary coverageUnary secondRoute
  exact ⟨sameSources, firstUnary, secondUnary, precisionPkg⟩

end BEDC.Derived.CompactUniformContinuityUp
