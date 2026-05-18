import BEDC.Derived.CompactUniformContinuityUp

namespace BEDC.Derived.CompactUniformContinuityUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem CompactUniformContinuityPacket_root_rational_fold_consumer [AskSetup] [PackageSetup]
    {source target graph tolerance precision net coverage modulusRows radiusRows fold transport route
      nameRow radiusRead consumer : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CompactUniformContinuityPacket source target graph tolerance precision net coverage
        modulusRows radiusRows fold transport route nameRow bundle pkg ->
      Cont radiusRows fold radiusRead ->
        Cont radiusRead precision consumer ->
          PkgSig bundle consumer pkg ->
            UnaryHistory radiusRows ∧ UnaryHistory fold ∧ UnaryHistory radiusRead ∧
              UnaryHistory consumer ∧ Cont modulusRows radiusRows fold ∧
                Cont radiusRows fold radiusRead ∧ Cont radiusRead precision consumer ∧
                  PkgSig bundle precision pkg ∧ PkgSig bundle consumer pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont UnaryHistory
  intro packet radiusRowsFoldRadiusRead radiusReadPrecisionConsumer consumerPkg
  obtain ⟨_sourceUnary, _targetUnary, _graphUnary, _toleranceUnary, netUnary, coverageUnary,
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
  have radiusReadUnary : UnaryHistory radiusRead :=
    unary_cont_closed radiusRowsUnary foldUnary radiusRowsFoldRadiusRead
  have consumerUnary : UnaryHistory consumer :=
    unary_cont_closed radiusReadUnary precisionUnary radiusReadPrecisionConsumer
  exact
    ⟨radiusRowsUnary, foldUnary, radiusReadUnary, consumerUnary, modulusRowsRadiusRowsFold,
      radiusRowsFoldRadiusRead, radiusReadPrecisionConsumer, precisionPkg, consumerPkg⟩

end BEDC.Derived.CompactUniformContinuityUp
