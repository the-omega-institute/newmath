import BEDC.Derived.CompactUniformContinuityUp

namespace BEDC.Derived.CompactUniformContinuityUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem CompactUniformContinuityPacket_root_pointwise_modulus_row
    [AskSetup] [PackageSetup]
    {source target graph tolerance precision net coverage modulusRows radiusRows fold transport
      route nameRow centerRead modulusRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CompactUniformContinuityPacket source target graph tolerance precision net coverage
        modulusRows radiusRows fold transport route nameRow bundle pkg ->
      Cont net coverage centerRead ->
        Cont centerRead graph modulusRead ->
          PkgSig bundle centerRead pkg ->
            PkgSig bundle modulusRead pkg ->
              UnaryHistory net ∧ UnaryHistory coverage ∧ UnaryHistory graph ∧
                UnaryHistory centerRead ∧ UnaryHistory modulusRead ∧
                  Cont net coverage centerRead ∧ Cont centerRead graph modulusRead ∧
                    PkgSig bundle precision pkg ∧ PkgSig bundle centerRead pkg ∧
                      PkgSig bundle modulusRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont UnaryHistory
  intro packet netCoverageCenter centerGraphModulus centerPkg modulusPkg
  obtain ⟨_sourceUnary, _targetUnary, graphUnary, _toleranceUnary, netUnary,
    coverageUnary, _radiusRowsUnary, _transportUnary, _nameRowUnary,
    _netCoverageModulusRows, _modulusRowsRadiusRowsFold, _foldTransportRoute,
    _routeNamePrecision, precisionPkg⟩ := packet
  have centerUnary : UnaryHistory centerRead :=
    unary_cont_closed netUnary coverageUnary netCoverageCenter
  have modulusUnary : UnaryHistory modulusRead :=
    unary_cont_closed centerUnary graphUnary centerGraphModulus
  exact
    ⟨netUnary, coverageUnary, graphUnary, centerUnary, modulusUnary,
      netCoverageCenter, centerGraphModulus, precisionPkg, centerPkg, modulusPkg⟩

end BEDC.Derived.CompactUniformContinuityUp
