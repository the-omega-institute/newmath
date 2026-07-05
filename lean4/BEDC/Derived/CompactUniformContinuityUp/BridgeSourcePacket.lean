import BEDC.Derived.CompactUniformContinuityUp

namespace BEDC.Derived.CompactUniformContinuityUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem CompactUniformContinuityPacket_bridge_source_packet [AskSetup] [PackageSetup]
    {source target graph tolerance precision net coverage modulusRows radiusRows fold transport
      route nameRow bridgeSource : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CompactUniformContinuityPacket source target graph tolerance precision net coverage
        modulusRows radiusRows fold transport route nameRow bundle pkg →
      Cont source target bridgeSource →
        PkgSig bundle bridgeSource pkg →
          UnaryHistory source ∧ UnaryHistory target ∧ UnaryHistory graph ∧
            UnaryHistory tolerance ∧ UnaryHistory precision ∧ UnaryHistory net ∧
              UnaryHistory coverage ∧ UnaryHistory modulusRows ∧ UnaryHistory radiusRows ∧
                UnaryHistory fold ∧ UnaryHistory transport ∧ UnaryHistory route ∧
                  UnaryHistory nameRow ∧ UnaryHistory bridgeSource ∧
                    Cont net coverage modulusRows ∧ Cont modulusRows radiusRows fold ∧
                      Cont fold transport route ∧ Cont route nameRow precision ∧
                        Cont source target bridgeSource ∧ PkgSig bundle precision pkg ∧
                          PkgSig bundle bridgeSource pkg := by
  -- BEDC touchpoint anchor: BHist Cont Pkg ProbeBundle
  intro packet sourceTargetBridgeSource bridgeSourcePkg
  obtain ⟨sourceUnary, targetUnary, graphUnary, toleranceUnary, netUnary, coverageUnary,
    radiusRowsUnary, transportUnary, nameRowUnary, netCoverageModulusRows,
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
  have bridgeSourceUnary : UnaryHistory bridgeSource :=
    unary_cont_closed sourceUnary targetUnary sourceTargetBridgeSource
  exact
    ⟨sourceUnary, targetUnary, graphUnary, toleranceUnary, precisionUnary, netUnary,
      coverageUnary, modulusRowsUnary, radiusRowsUnary, foldUnary, transportUnary, routeUnary,
      nameRowUnary, bridgeSourceUnary, netCoverageModulusRows, modulusRowsRadiusRowsFold,
      foldTransportRoute, routeNamePrecision, sourceTargetBridgeSource, precisionPkg,
      bridgeSourcePkg⟩

theorem CompactUniformContinuityPacket_StdBridge [AskSetup] [PackageSetup]
    {source target graph tolerance precision net coverage modulusRows radiusRows fold transport
      route nameRow metricRead realRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CompactUniformContinuityPacket source target graph tolerance precision net coverage
        modulusRows radiusRows fold transport route nameRow bundle pkg →
      Cont precision nameRow metricRead →
        Cont metricRead transport realRead →
          PkgSig bundle realRead pkg →
            SemanticNameCert
                (fun row : BHist => hsame row precision ∧ UnaryHistory row ∧
                  PkgSig bundle row pkg)
                (fun row : BHist =>
                  Cont route nameRow row ∧ Cont net coverage modulusRows ∧
                    Cont modulusRows radiusRows fold)
                (fun row : BHist =>
                  PkgSig bundle row pkg ∧ Cont fold transport route ∧
                    Cont route nameRow precision)
                (fun row row' : BHist => hsame row row') ∧
              UnaryHistory metricRead ∧ UnaryHistory realRead ∧
                Cont precision nameRow metricRead ∧ Cont metricRead transport realRead := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig hsame SemanticNameCert UnaryHistory
  intro packet precisionNameMetric metricTransportReal realReadPkg
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
  have metricUnary : UnaryHistory metricRead :=
    unary_cont_closed precisionUnary nameRowUnary precisionNameMetric
  have realUnary : UnaryHistory realRead :=
    unary_cont_closed metricUnary transportUnary metricTransportReal
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row precision ∧ UnaryHistory row ∧
            PkgSig bundle row pkg)
          (fun row : BHist =>
            Cont route nameRow row ∧ Cont net coverage modulusRows ∧
              Cont modulusRows radiusRows fold)
          (fun row : BHist =>
            PkgSig bundle row pkg ∧ Cont fold transport route ∧
              Cont route nameRow precision)
          (fun row row' : BHist => hsame row row') := {
    core := {
      carrier_inhabited := ⟨precision, hsame_refl precision, precisionUnary, precisionPkg⟩
      equiv_refl := by
        intro row _sourceRow
        exact hsame_refl row
      equiv_symm := by
        intro _row _row' same
        exact hsame_symm same
      equiv_trans := by
        intro _row _row' _row'' leftSame rightSame
        exact hsame_trans leftSame rightSame
      carrier_respects_equiv := by
        intro _row _row' same sourceRow
        cases same
        exact sourceRow
    }
    pattern_sound := by
      intro _row sourceRow
      exact
        ⟨cont_result_hsame_transport routeNamePrecision (hsame_symm sourceRow.left),
          netCoverageModulusRows, modulusRowsRadiusRowsFold⟩
    ledger_sound := by
      intro _row sourceRow
      cases sourceRow.left
      exact ⟨sourceRow.right.right, foldTransportRoute, routeNamePrecision⟩
  }
  exact ⟨cert, metricUnary, realUnary, precisionNameMetric, metricTransportReal⟩

end BEDC.Derived.CompactUniformContinuityUp
