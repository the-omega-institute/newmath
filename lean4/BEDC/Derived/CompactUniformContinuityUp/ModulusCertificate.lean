import BEDC.Derived.CompactUniformContinuityUp

namespace BEDC.Derived.CompactUniformContinuityUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem CompactUniformContinuityPacket_modulus_certificate [AskSetup] [PackageSetup]
    {source target graph tolerance precision net coverage modulusRows radiusRows fold transport
      route nameRow handoff targetRead radiusRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CompactUniformContinuityPacket source target graph tolerance precision net coverage
        modulusRows radiusRows fold transport route nameRow bundle pkg ->
      Cont precision net handoff ->
        Cont handoff target targetRead ->
          Cont radiusRows fold radiusRead ->
            PkgSig bundle targetRead pkg ->
              PkgSig bundle radiusRead pkg ->
                SemanticNameCert
                  (fun row : BHist => hsame row targetRead ∧ UnaryHistory row)
                  (fun row : BHist =>
                    Cont precision net handoff ∧ Cont handoff target row ∧
                      Cont radiusRows fold radiusRead)
                  (fun row : BHist =>
                    PkgSig bundle row pkg ∧ PkgSig bundle radiusRead pkg ∧
                      PkgSig bundle precision pkg)
                  hsame := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame SemanticNameCert
  intro packet precisionNetHandoff handoffTargetRead radiusRowsFoldRadiusRead targetReadPkg
    radiusReadPkg
  obtain ⟨_sourceUnary, targetUnary, _graphUnary, _toleranceUnary, netUnary,
    coverageUnary, radiusRowsUnary, transportUnary, nameRowUnary, netCoverageModulusRows,
    modulusRowsRadiusRowsFold, foldTransportRoute, routeNamePrecision, precisionPkg⟩ := packet
  have modulusRowsUnary : UnaryHistory modulusRows :=
    unary_cont_closed netUnary coverageUnary netCoverageModulusRows
  have foldUnary : UnaryHistory fold :=
    unary_cont_closed modulusRowsUnary radiusRowsUnary modulusRowsRadiusRowsFold
  have routeUnary : UnaryHistory route :=
    unary_cont_closed foldUnary transportUnary foldTransportRoute
  have precisionUnary : UnaryHistory precision :=
    unary_cont_closed routeUnary nameRowUnary routeNamePrecision
  have handoffUnary : UnaryHistory handoff :=
    unary_cont_closed precisionUnary netUnary precisionNetHandoff
  have targetReadUnary : UnaryHistory targetRead :=
    unary_cont_closed handoffUnary targetUnary handoffTargetRead
  exact {
    core := {
      carrier_inhabited := Exists.intro targetRead ⟨hsame_refl targetRead, targetReadUnary⟩
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
      intro row sourceRow
      cases sourceRow.left
      exact ⟨precisionNetHandoff, handoffTargetRead, radiusRowsFoldRadiusRead⟩
    ledger_sound := by
      intro row sourceRow
      cases sourceRow.left
      exact ⟨targetReadPkg, radiusReadPkg, precisionPkg⟩
  }

end BEDC.Derived.CompactUniformContinuityUp
