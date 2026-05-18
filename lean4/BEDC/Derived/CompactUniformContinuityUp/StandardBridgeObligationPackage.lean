import BEDC.Derived.CompactUniformContinuityUp

namespace BEDC.Derived.CompactUniformContinuityUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem CompactUniformContinuityPacket_standard_bridge_obligation_package
    [AskSetup] [PackageSetup]
    {source target graph tolerance precision net coverage modulusRows radiusRows fold transport
      route nameRow bridgeSource realRead radiusRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CompactUniformContinuityPacket source target graph tolerance precision net coverage
        modulusRows radiusRows fold transport route nameRow bundle pkg →
      Cont source target bridgeSource →
        Cont precision nameRow realRead →
          Cont radiusRows fold radiusRead →
            PkgSig bundle bridgeSource pkg →
              PkgSig bundle realRead pkg →
                PkgSig bundle radiusRead pkg →
                  SemanticNameCert
                    (fun row : BHist => hsame row bridgeSource ∧ UnaryHistory row)
                    (fun row : BHist =>
                      Cont source target row ∧ Cont net coverage modulusRows ∧
                        Cont modulusRows radiusRows fold)
                    (fun row : BHist =>
                      PkgSig bundle row pkg ∧ PkgSig bundle precision pkg ∧
                        PkgSig bundle radiusRead pkg)
                    hsame := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle Pkg SemanticNameCert hsame
  intro packet sourceTargetBridge precisionNameReal radiusFoldRead bridgeSourcePkg realReadPkg
    radiusReadPkg
  obtain ⟨sourceUnary, targetUnary, _graphUnary, _toleranceUnary, netUnary, coverageUnary,
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
    unary_cont_closed sourceUnary targetUnary sourceTargetBridge
  have realReadUnary : UnaryHistory realRead :=
    unary_cont_closed precisionUnary nameRowUnary precisionNameReal
  have radiusReadUnary : UnaryHistory radiusRead :=
    unary_cont_closed radiusRowsUnary foldUnary radiusFoldRead
  have bridgeSourcePkgRealReadRadiusRead :
      PkgSig bundle bridgeSource pkg ∧ PkgSig bundle realRead pkg ∧
        PkgSig bundle radiusRead pkg :=
    ⟨bridgeSourcePkg, realReadPkg, radiusReadPkg⟩
  have bridgeSourceRealReadRadiusReadUnary :
      UnaryHistory bridgeSource ∧ UnaryHistory realRead ∧ UnaryHistory radiusRead :=
    ⟨bridgeSourceUnary, realReadUnary, radiusReadUnary⟩
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
        cases same
        exact sourceRow
    }
    pattern_sound := by
      intro _row sourceRow
      exact
        ⟨cont_result_hsame_transport sourceTargetBridge (hsame_symm sourceRow.left),
          netCoverageModulusRows, modulusRowsRadiusRowsFold⟩
    ledger_sound := by
      intro _row sourceRow
      cases sourceRow.left
      exact
        ⟨bridgeSourcePkgRealReadRadiusRead.left, precisionPkg,
          bridgeSourcePkgRealReadRadiusRead.right.right⟩
  }

end BEDC.Derived.CompactUniformContinuityUp
