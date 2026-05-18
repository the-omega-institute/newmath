import BEDC.Derived.CompactUniformContinuityUp

namespace BEDC.Derived.CompactUniformContinuityUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem CompactUniformContinuityPacket_compact_continuous_namecert_export [AskSetup]
    [PackageSetup]
    {source target graph tolerance precision net coverage modulusRows radiusRows fold transport
      route nameRow sourceRead targetRead realRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CompactUniformContinuityPacket source target graph tolerance precision net coverage
        modulusRows radiusRows fold transport route nameRow bundle pkg ->
      Cont source net sourceRead ->
        Cont precision target targetRead ->
          Cont precision transport realRead ->
            PkgSig bundle sourceRead pkg ->
              PkgSig bundle targetRead pkg ->
                PkgSig bundle realRead pkg ->
                  SemanticNameCert
                    (fun row : BHist =>
                      hsame row precision ∧ UnaryHistory row ∧ PkgSig bundle row pkg)
                    (fun row : BHist =>
                      Cont route nameRow row ∧ Cont net coverage modulusRows ∧
                        Cont modulusRows radiusRows fold)
                    (fun row : BHist =>
                      PkgSig bundle row pkg ∧ Cont fold transport route ∧
                        Cont source net sourceRead ∧ Cont precision target targetRead ∧
                          Cont precision transport realRead)
                    (fun row row' : BHist => hsame row row') := by
  -- BEDC touchpoint anchor: BHist SemanticNameCert Cont Pkg ProbeBundle hsame
  intro packet sourceNetRead precisionTargetRead precisionTransportRead sourcePkg targetPkg realPkg
  obtain ⟨sourceUnary, _targetUnary, _graphUnary, _toleranceUnary, netUnary, coverageUnary,
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
  exact {
    core := {
      carrier_inhabited :=
        Exists.intro precision ⟨hsame_refl precision, precisionUnary, precisionPkg⟩
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
      exact
        ⟨sourceRow.right.right, foldTransportRoute, sourceNetRead, precisionTargetRead,
          precisionTransportRead⟩
  }

end BEDC.Derived.CompactUniformContinuityUp
