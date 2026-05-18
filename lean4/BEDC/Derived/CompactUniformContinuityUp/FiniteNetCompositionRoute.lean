import BEDC.Derived.CompactUniformContinuityUp

namespace BEDC.Derived.CompactUniformContinuityUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem CompactUniformContinuityPacket_finite_net_composition_route
    [AskSetup] [PackageSetup]
    {source mid target graph tolerance precision net coverage modulusRows radiusRows fold
      transport route nameRow leftBridge compositeBridge foldedPrecision realRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CompactUniformContinuityPacket source mid graph tolerance precision net coverage
        modulusRows radiusRows fold transport route nameRow bundle pkg →
      UnaryHistory target →
        Cont source mid leftBridge →
          Cont leftBridge target compositeBridge →
            Cont radiusRows fold foldedPrecision →
              Cont precision nameRow realRead →
                hsame foldedPrecision precision →
                  PkgSig bundle compositeBridge pkg →
                    PkgSig bundle foldedPrecision pkg →
                      PkgSig bundle realRead pkg →
                        SemanticNameCert
                            (fun row : BHist => hsame row compositeBridge ∧ UnaryHistory row)
                            (fun row : BHist =>
                              Cont leftBridge target row ∧ Cont net coverage modulusRows ∧
                                Cont modulusRows radiusRows fold)
                            (fun row : BHist =>
                              PkgSig bundle row pkg ∧ PkgSig bundle precision pkg ∧
                                PkgSig bundle foldedPrecision pkg)
                            hsame ∧
                          UnaryHistory leftBridge ∧ UnaryHistory compositeBridge ∧
                            UnaryHistory foldedPrecision ∧ Cont source mid leftBridge ∧
                              Cont leftBridge target compositeBridge ∧
                                Cont radiusRows fold foldedPrecision ∧
                                  hsame foldedPrecision precision ∧
                                    PkgSig bundle precision pkg ∧
                                      PkgSig bundle compositeBridge pkg ∧
                                        PkgSig bundle foldedPrecision pkg := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle Pkg SemanticNameCert hsame
  intro packet targetUnary sourceMidLeft leftTargetComposite radiusFoldPrecision
    precisionNameReal foldedSamePrecision compositePkg foldedPrecisionPkg _realReadPkg
  obtain ⟨sourceUnary, midUnary, _graphUnary, _toleranceUnary, netUnary, coverageUnary,
    radiusRowsUnary, _transportUnary, _nameRowUnary, netCoverageModulusRows,
    modulusRowsRadiusRowsFold, _foldTransportRoute, _routeNamePrecision, precisionPkg⟩ :=
      packet
  have modulusRowsUnary : UnaryHistory modulusRows :=
    unary_cont_closed netUnary coverageUnary netCoverageModulusRows
  have foldUnary : UnaryHistory fold :=
    unary_cont_closed modulusRowsUnary radiusRowsUnary modulusRowsRadiusRowsFold
  have leftBridgeUnary : UnaryHistory leftBridge :=
    unary_cont_closed sourceUnary midUnary sourceMidLeft
  have compositeBridgeUnary : UnaryHistory compositeBridge :=
    unary_cont_closed leftBridgeUnary targetUnary leftTargetComposite
  have foldedPrecisionUnary : UnaryHistory foldedPrecision :=
    unary_cont_closed radiusRowsUnary foldUnary radiusFoldPrecision
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row compositeBridge ∧ UnaryHistory row)
          (fun row : BHist =>
            Cont leftBridge target row ∧ Cont net coverage modulusRows ∧
              Cont modulusRows radiusRows fold)
          (fun row : BHist =>
            PkgSig bundle row pkg ∧ PkgSig bundle precision pkg ∧
              PkgSig bundle foldedPrecision pkg)
          hsame := by
    exact {
      core := {
        carrier_inhabited :=
          Exists.intro compositeBridge ⟨hsame_refl compositeBridge, compositeBridgeUnary⟩
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
          ⟨cont_result_hsame_transport leftTargetComposite (hsame_symm sourceRow.left),
            netCoverageModulusRows, modulusRowsRadiusRowsFold⟩
      ledger_sound := by
        intro _row sourceRow
        cases sourceRow.left
        exact ⟨compositePkg, precisionPkg, foldedPrecisionPkg⟩
    }
  exact
    ⟨cert, leftBridgeUnary, compositeBridgeUnary, foldedPrecisionUnary, sourceMidLeft,
      leftTargetComposite, radiusFoldPrecision, foldedSamePrecision, precisionPkg,
      compositePkg, foldedPrecisionPkg⟩

end BEDC.Derived.CompactUniformContinuityUp
