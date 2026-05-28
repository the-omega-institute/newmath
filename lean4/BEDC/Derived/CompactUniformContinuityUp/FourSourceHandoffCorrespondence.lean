import BEDC.Derived.CompactUniformContinuityUp

namespace BEDC.Derived.CompactUniformContinuityUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem CompactUniformContinuityPacket_four_source_handoff_correspondence
    [AskSetup] [PackageSetup]
    {source target graph tolerance precision net coverage modulusRows radiusRows fold transport
      route nameRow compactRead continuousRead metricRead rationalRead realRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CompactUniformContinuityPacket source target graph tolerance precision net coverage
        modulusRows radiusRows fold transport route nameRow bundle pkg ->
      Cont net coverage compactRead ->
        Cont compactRead graph continuousRead ->
          Cont continuousRead target metricRead ->
            Cont radiusRows fold rationalRead ->
              Cont rationalRead metricRead realRead ->
                PkgSig bundle realRead pkg ->
                  UnaryHistory compactRead ∧ UnaryHistory continuousRead ∧
                    UnaryHistory metricRead ∧ UnaryHistory rationalRead ∧
                      UnaryHistory realRead ∧ Cont net coverage compactRead ∧
                        Cont compactRead graph continuousRead ∧
                          Cont continuousRead target metricRead ∧
                            Cont radiusRows fold rationalRead ∧
                              Cont rationalRead metricRead realRead ∧
                                PkgSig bundle precision pkg ∧
                                  PkgSig bundle realRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg UnaryHistory Cont PkgSig
  intro packet netCoverageCompact compactGraphContinuous continuousTargetMetric
    radiusFoldRational rationalMetricReal realPkg
  obtain
    ⟨_sourceUnary, targetUnary, graphUnary, _toleranceUnary, netUnary, coverageUnary,
      radiusRowsUnary, transportUnary, _nameRowUnary, netCoverageModulusRows,
      modulusRowsRadiusRowsFold, foldTransportRoute, _routeNamePrecision, precisionPkg⟩ :=
      packet
  have compactReadUnary : UnaryHistory compactRead :=
    unary_cont_closed netUnary coverageUnary netCoverageCompact
  have continuousReadUnary : UnaryHistory continuousRead :=
    unary_cont_closed compactReadUnary graphUnary compactGraphContinuous
  have metricReadUnary : UnaryHistory metricRead :=
    unary_cont_closed continuousReadUnary targetUnary continuousTargetMetric
  have modulusRowsUnary : UnaryHistory modulusRows :=
    unary_cont_closed netUnary coverageUnary netCoverageModulusRows
  have foldUnary : UnaryHistory fold :=
    unary_cont_closed modulusRowsUnary radiusRowsUnary modulusRowsRadiusRowsFold
  have _routeUnary : UnaryHistory route :=
    unary_cont_closed foldUnary transportUnary foldTransportRoute
  have rationalReadUnary : UnaryHistory rationalRead :=
    unary_cont_closed radiusRowsUnary foldUnary radiusFoldRational
  have realReadUnary : UnaryHistory realRead :=
    unary_cont_closed rationalReadUnary metricReadUnary rationalMetricReal
  exact
    ⟨compactReadUnary, continuousReadUnary, metricReadUnary, rationalReadUnary,
      realReadUnary, netCoverageCompact, compactGraphContinuous, continuousTargetMetric,
      radiusFoldRational, rationalMetricReal, precisionPkg, realPkg⟩

theorem CompactUniformContinuityPacket_four_source_bridge_determinacy
    [AskSetup] [PackageSetup]
    {source target graph tolerance precision net coverage modulusRows radiusRows fold transport
      route nameRow sourceRead targetRead metricRead realRead radiusRead bridgeRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CompactUniformContinuityPacket source target graph tolerance precision net coverage
        modulusRows radiusRows fold transport route nameRow bundle pkg ->
      Cont source net sourceRead ->
        Cont precision target targetRead ->
          Cont precision nameRow metricRead ->
            Cont metricRead transport realRead ->
              Cont radiusRows fold radiusRead ->
                Cont sourceRead realRead bridgeRead ->
                  PkgSig bundle sourceRead pkg ->
                    PkgSig bundle targetRead pkg ->
                      PkgSig bundle realRead pkg ->
                        PkgSig bundle radiusRead pkg ->
                          PkgSig bundle bridgeRead pkg ->
                            SemanticNameCert
                                (fun row : BHist => hsame row bridgeRead ∧ UnaryHistory row)
                                (fun row : BHist =>
                                  hsame row sourceRead ∨ hsame row targetRead ∨
                                    hsame row metricRead ∨ hsame row realRead ∨
                                      hsame row radiusRead ∨ hsame row bridgeRead)
                                (fun row : BHist =>
                                  PkgSig bundle row pkg ∧ PkgSig bundle bridgeRead pkg)
                                hsame ∧
                              UnaryHistory bridgeRead ∧ PkgSig bundle bridgeRead pkg := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle PkgSig SemanticNameCert hsame UnaryHistory
  intro packet sourceNetRead precisionTargetRead precisionNameMetric metricTransportReal
    radiusRowsFoldRadiusRead sourceReadRealBridge sourceReadPkg _targetReadPkg _realReadPkg
    _radiusReadPkg bridgeReadPkg
  obtain ⟨sourceUnary, targetUnary, _graphUnary, _toleranceUnary, netUnary, coverageUnary,
    radiusRowsUnary, transportUnary, nameRowUnary, netCoverageModulusRows,
    modulusRowsRadiusRowsFold, foldTransportRoute, routeNamePrecision, _precisionPkg⟩ :=
      packet
  have modulusRowsUnary : UnaryHistory modulusRows :=
    unary_cont_closed netUnary coverageUnary netCoverageModulusRows
  have foldUnary : UnaryHistory fold :=
    unary_cont_closed modulusRowsUnary radiusRowsUnary modulusRowsRadiusRowsFold
  have routeUnary : UnaryHistory route :=
    unary_cont_closed foldUnary transportUnary foldTransportRoute
  have precisionUnary : UnaryHistory precision :=
    unary_cont_closed routeUnary nameRowUnary routeNamePrecision
  have sourceReadUnary : UnaryHistory sourceRead :=
    unary_cont_closed sourceUnary netUnary sourceNetRead
  have _targetReadUnary : UnaryHistory targetRead :=
    unary_cont_closed precisionUnary targetUnary precisionTargetRead
  have metricReadUnary : UnaryHistory metricRead :=
    unary_cont_closed precisionUnary nameRowUnary precisionNameMetric
  have realReadUnary : UnaryHistory realRead :=
    unary_cont_closed metricReadUnary transportUnary metricTransportReal
  have _radiusReadUnary : UnaryHistory radiusRead :=
    unary_cont_closed radiusRowsUnary foldUnary radiusRowsFoldRadiusRead
  have bridgeReadUnary : UnaryHistory bridgeRead :=
    unary_cont_closed sourceReadUnary realReadUnary sourceReadRealBridge
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row bridgeRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row sourceRead ∨ hsame row targetRead ∨ hsame row metricRead ∨
              hsame row realRead ∨ hsame row radiusRead ∨ hsame row bridgeRead)
          (fun row : BHist => PkgSig bundle row pkg ∧ PkgSig bundle bridgeRead pkg)
          hsame := {
    core := {
      carrier_inhabited :=
        Exists.intro bridgeRead ⟨hsame_refl bridgeRead, bridgeReadUnary⟩
      equiv_refl := by
        intro row _source
        exact hsame_refl row
      equiv_symm := by
        intro _row _other sameRows
        exact hsame_symm sameRows
      equiv_trans := by
        intro _row _middle _other sameLeft sameRight
        exact hsame_trans sameLeft sameRight
      carrier_respects_equiv := by
        intro _row _other sameRows source
        exact
          ⟨hsame_trans (hsame_symm sameRows) source.left,
            unary_transport source.right sameRows⟩
    }
    pattern_sound := by
      intro _row source
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr source.left))))
    ledger_sound := by
      intro _row source
      cases source.left
      exact ⟨bridgeReadPkg, bridgeReadPkg⟩
  }
  exact ⟨cert, bridgeReadUnary, bridgeReadPkg⟩

end BEDC.Derived.CompactUniformContinuityUp
