import BEDC.Derived.CompactUniformContinuityUp

namespace BEDC.Derived.CompactUniformContinuityUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem CompactUniformContinuityPacket_rational_fold_metric_compatibility
    [AskSetup] [PackageSetup]
    {source target graph tolerance precision net coverage modulusRows radiusRows fold transport
      route nameRow radiusRead targetRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CompactUniformContinuityPacket source target graph tolerance precision net coverage
        modulusRows radiusRows fold transport route nameRow bundle pkg ->
      Cont radiusRows fold radiusRead ->
        Cont precision target targetRead ->
          PkgSig bundle radiusRead pkg ->
            PkgSig bundle targetRead pkg ->
              UnaryHistory precision ∧ UnaryHistory radiusRows ∧ UnaryHistory fold ∧
                UnaryHistory radiusRead ∧ UnaryHistory targetRead ∧
                  Cont modulusRows radiusRows fold ∧ Cont radiusRows fold radiusRead ∧
                    Cont precision target targetRead ∧ PkgSig bundle precision pkg ∧
                      PkgSig bundle radiusRead pkg ∧ PkgSig bundle targetRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont UnaryHistory
  intro packet radiusRowsFoldRadiusRead precisionTargetRead radiusReadPkg targetReadPkg
  obtain ⟨_sourceUnary, targetUnary, _graphUnary, _toleranceUnary, netUnary,
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
  have radiusReadUnary : UnaryHistory radiusRead :=
    unary_cont_closed radiusRowsUnary foldUnary radiusRowsFoldRadiusRead
  have targetReadUnary : UnaryHistory targetRead :=
    unary_cont_closed precisionUnary targetUnary precisionTargetRead
  exact
    ⟨precisionUnary, radiusRowsUnary, foldUnary, radiusReadUnary, targetReadUnary,
      modulusRowsRadiusRowsFold, radiusRowsFoldRadiusRead, precisionTargetRead, precisionPkg,
      radiusReadPkg, targetReadPkg⟩

end BEDC.Derived.CompactUniformContinuityUp
