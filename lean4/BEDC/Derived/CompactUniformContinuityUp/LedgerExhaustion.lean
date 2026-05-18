import BEDC.Derived.CompactUniformContinuityUp

namespace BEDC.Derived.CompactUniformContinuityUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem CompactUniformContinuityPacket_namecert_ledger_exhaustion [AskSetup] [PackageSetup]
    {source target graph tolerance precision net coverage modulusRows radiusRows fold transport
      route nameRow metricRead realRead radiusRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CompactUniformContinuityPacket source target graph tolerance precision net coverage
        modulusRows radiusRows fold transport route nameRow bundle pkg ->
      Cont precision nameRow metricRead ->
        Cont metricRead transport realRead ->
          Cont radiusRows fold radiusRead ->
            PkgSig bundle realRead pkg ->
              PkgSig bundle radiusRead pkg ->
                UnaryHistory net ∧ UnaryHistory coverage ∧ UnaryHistory modulusRows ∧
                  UnaryHistory radiusRows ∧ UnaryHistory fold ∧ UnaryHistory route ∧
                    UnaryHistory precision ∧ UnaryHistory metricRead ∧ UnaryHistory realRead ∧
                      UnaryHistory radiusRead ∧ Cont net coverage modulusRows ∧
                        Cont modulusRows radiusRows fold ∧ Cont fold transport route ∧
                          Cont route nameRow precision ∧ Cont precision nameRow metricRead ∧
                            Cont metricRead transport realRead ∧
                              Cont radiusRows fold radiusRead ∧ PkgSig bundle precision pkg ∧
                                PkgSig bundle realRead pkg ∧ PkgSig bundle radiusRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont UnaryHistory
  intro packet precisionNameMetric metricTransportReal radiusRowsFoldRadiusRead realReadPkg
    radiusReadPkg
  obtain ⟨_sourceUnary, _targetUnary, _graphUnary, _toleranceUnary, netUnary,
    coverageUnary, radiusRowsUnary, transportUnary, nameRowUnary, netCoverageModulusRows,
    modulusRowsRadiusRowsFold, foldTransportRoute, routeNamePrecision, precisionPkg⟩ :=
      packet
  have modulusRowsUnary : UnaryHistory modulusRows :=
    unary_cont_closed netUnary coverageUnary netCoverageModulusRows
  have foldUnary : UnaryHistory fold :=
    unary_cont_closed modulusRowsUnary radiusRowsUnary modulusRowsRadiusRowsFold
  have routeUnary : UnaryHistory route :=
    unary_cont_closed foldUnary transportUnary foldTransportRoute
  have precisionUnary : UnaryHistory precision :=
    unary_cont_closed routeUnary nameRowUnary routeNamePrecision
  have metricReadUnary : UnaryHistory metricRead :=
    unary_cont_closed precisionUnary nameRowUnary precisionNameMetric
  have realReadUnary : UnaryHistory realRead :=
    unary_cont_closed metricReadUnary transportUnary metricTransportReal
  have radiusReadUnary : UnaryHistory radiusRead :=
    unary_cont_closed radiusRowsUnary foldUnary radiusRowsFoldRadiusRead
  exact
    ⟨netUnary, coverageUnary, modulusRowsUnary, radiusRowsUnary, foldUnary, routeUnary,
      precisionUnary, metricReadUnary, realReadUnary, radiusReadUnary, netCoverageModulusRows,
      modulusRowsRadiusRowsFold, foldTransportRoute, routeNamePrecision, precisionNameMetric,
      metricTransportReal, radiusRowsFoldRadiusRead, precisionPkg, realReadPkg, radiusReadPkg⟩

theorem CompactUniformContinuityPacket_modulus_ledger_exhaustion [AskSetup] [PackageSetup]
    {source target graph tolerance precision net coverage modulusRows radiusRows fold transport
      route nameRow centerRead metricRead targetRead radiusRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CompactUniformContinuityPacket source target graph tolerance precision net coverage
        modulusRows radiusRows fold transport route nameRow bundle pkg ->
      Cont net coverage centerRead ->
        Cont centerRead target metricRead ->
          Cont metricRead transport targetRead ->
            Cont modulusRows radiusRows fold ->
              Cont radiusRows fold radiusRead ->
                PkgSig bundle targetRead pkg ->
                  PkgSig bundle radiusRead pkg ->
                    UnaryHistory centerRead ∧ UnaryHistory metricRead ∧
                      UnaryHistory targetRead ∧ UnaryHistory fold ∧
                        UnaryHistory radiusRead ∧ Cont net coverage centerRead ∧
                          Cont centerRead target metricRead ∧
                            Cont metricRead transport targetRead ∧
                              Cont modulusRows radiusRows fold ∧
                                Cont radiusRows fold radiusRead ∧
                                  PkgSig bundle precision pkg ∧
                                    PkgSig bundle targetRead pkg ∧
                                      PkgSig bundle radiusRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont UnaryHistory
  intro packet netCoverageCenter centerTargetMetric metricTransportTarget
    modulusRowsRadiusRowsFold radiusRowsFoldRadiusRead targetReadPkg radiusReadPkg
  obtain ⟨_sourceUnary, targetUnary, _graphUnary, _toleranceUnary, netUnary,
    coverageUnary, radiusRowsUnary, transportUnary, _nameRowUnary, netCoverageModulusRows,
    _packetModulusRowsRadiusRowsFold, _foldTransportRoute, _routeNamePrecision,
    precisionPkg⟩ := packet
  have centerReadUnary : UnaryHistory centerRead :=
    unary_cont_closed netUnary coverageUnary netCoverageCenter
  have metricReadUnary : UnaryHistory metricRead :=
    unary_cont_closed centerReadUnary targetUnary centerTargetMetric
  have targetReadUnary : UnaryHistory targetRead :=
    unary_cont_closed metricReadUnary transportUnary metricTransportTarget
  have modulusRowsUnary : UnaryHistory modulusRows :=
    unary_cont_closed netUnary coverageUnary netCoverageModulusRows
  have foldUnary : UnaryHistory fold :=
    unary_cont_closed modulusRowsUnary radiusRowsUnary modulusRowsRadiusRowsFold
  have radiusReadUnary : UnaryHistory radiusRead :=
    unary_cont_closed radiusRowsUnary foldUnary radiusRowsFoldRadiusRead
  exact
    ⟨centerReadUnary, metricReadUnary, targetReadUnary, foldUnary, radiusReadUnary,
      netCoverageCenter, centerTargetMetric, metricTransportTarget, modulusRowsRadiusRowsFold,
      radiusRowsFoldRadiusRead, precisionPkg, targetReadPkg, radiusReadPkg⟩

end BEDC.Derived.CompactUniformContinuityUp
