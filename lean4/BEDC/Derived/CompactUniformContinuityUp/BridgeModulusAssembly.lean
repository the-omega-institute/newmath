import BEDC.Derived.CompactUniformContinuityUp

namespace BEDC.Derived.CompactUniformContinuityUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem CompactUniformContinuityPacket_bridge_modulus_assembly [AskSetup] [PackageSetup]
    {source target graph tolerance precision net coverage modulusRows radiusRows fold transport
      route nameRow bridgeSource centerRead radiusRead foldedPrecision realRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CompactUniformContinuityPacket source target graph tolerance precision net coverage
        modulusRows radiusRows fold transport route nameRow bundle pkg →
      Cont source target bridgeSource →
        Cont net coverage centerRead →
          Cont centerRead radiusRows radiusRead →
            Cont radiusRows fold foldedPrecision →
              Cont precision nameRow realRead →
                hsame foldedPrecision precision →
                  PkgSig bundle bridgeSource pkg →
                    PkgSig bundle centerRead pkg →
                      PkgSig bundle radiusRead pkg →
                        PkgSig bundle foldedPrecision pkg →
                          PkgSig bundle realRead pkg →
                            SemanticNameCert
                                (fun row : BHist => hsame row bridgeSource ∧ UnaryHistory row)
                                (fun row : BHist =>
                                  Cont source target row ∧ Cont net coverage modulusRows ∧
                                    Cont modulusRows radiusRows fold)
                                (fun row : BHist =>
                                  PkgSig bundle row pkg ∧ PkgSig bundle precision pkg ∧
                                    PkgSig bundle radiusRead pkg)
                                hsame ∧
                              UnaryHistory bridgeSource ∧ UnaryHistory centerRead ∧
                                UnaryHistory radiusRead ∧ UnaryHistory foldedPrecision ∧
                                  Cont source target bridgeSource ∧
                                    Cont net coverage centerRead ∧
                                      Cont centerRead radiusRows radiusRead ∧
                                        Cont radiusRows fold foldedPrecision ∧
                                          hsame foldedPrecision precision ∧
                                            PkgSig bundle precision pkg ∧
                                              PkgSig bundle bridgeSource pkg ∧
                                                PkgSig bundle foldedPrecision pkg := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle Pkg SemanticNameCert hsame
  intro packet sourceTargetBridge netCoverageCenter centerRadiusRead radiusFoldPrecision
    precisionNameReal foldedSamePrecision bridgeSourcePkg _centerPkg radiusReadPkg
    foldedPrecisionPkg _realReadPkg
  obtain ⟨sourceUnary, targetUnary, _graphUnary, _toleranceUnary, netUnary, coverageUnary,
    radiusRowsUnary, _transportUnary, nameRowUnary, netCoverageModulusRows,
    modulusRowsRadiusRowsFold, _foldTransportRoute, _routeNamePrecision, precisionPkg⟩ :=
      packet
  have modulusRowsUnary : UnaryHistory modulusRows :=
    unary_cont_closed netUnary coverageUnary netCoverageModulusRows
  have foldUnary : UnaryHistory fold :=
    unary_cont_closed modulusRowsUnary radiusRowsUnary modulusRowsRadiusRowsFold
  have bridgeSourceUnary : UnaryHistory bridgeSource :=
    unary_cont_closed sourceUnary targetUnary sourceTargetBridge
  have centerUnary : UnaryHistory centerRead :=
    unary_cont_closed netUnary coverageUnary netCoverageCenter
  have radiusReadUnary : UnaryHistory radiusRead :=
    unary_cont_closed centerUnary radiusRowsUnary centerRadiusRead
  have foldedPrecisionUnary : UnaryHistory foldedPrecision :=
    unary_cont_closed radiusRowsUnary foldUnary radiusFoldPrecision
  have precisionUnary : UnaryHistory precision :=
    unary_transport foldedPrecisionUnary foldedSamePrecision
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row bridgeSource ∧ UnaryHistory row)
          (fun row : BHist =>
            Cont source target row ∧ Cont net coverage modulusRows ∧
              Cont modulusRows radiusRows fold)
          (fun row : BHist =>
            PkgSig bundle row pkg ∧ PkgSig bundle precision pkg ∧
              PkgSig bundle radiusRead pkg)
          hsame := by
    exact {
      core := {
        carrier_inhabited :=
          Exists.intro bridgeSource ⟨hsame_refl bridgeSource, bridgeSourceUnary⟩
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
          exact ⟨hsame_trans (hsame_symm same) sourceRow.left,
            unary_transport sourceRow.right same⟩
      }
      pattern_sound := by
        intro _row sourceRow
        exact
          ⟨cont_result_hsame_transport sourceTargetBridge (hsame_symm sourceRow.left),
            netCoverageModulusRows, modulusRowsRadiusRowsFold⟩
      ledger_sound := by
        intro _row sourceRow
        cases sourceRow.left
        exact ⟨bridgeSourcePkg, precisionPkg, radiusReadPkg⟩
    }
  exact
    ⟨cert, bridgeSourceUnary, centerUnary, radiusReadUnary, foldedPrecisionUnary,
      sourceTargetBridge, netCoverageCenter, centerRadiusRead, radiusFoldPrecision,
      foldedSamePrecision, precisionPkg, bridgeSourcePkg, foldedPrecisionPkg⟩

end BEDC.Derived.CompactUniformContinuityUp
