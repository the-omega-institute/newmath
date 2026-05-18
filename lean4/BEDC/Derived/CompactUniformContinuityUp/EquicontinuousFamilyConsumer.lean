import BEDC.Derived.CompactUniformContinuityUp

namespace BEDC.Derived.CompactUniformContinuityUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem CompactUniformContinuityPacket_equicontinuous_family_consumer [AskSetup] [PackageSetup]
    {source target graph tolerance precision net coverage modulusRows radiusRows fold transport route
      nameRow familyMember sourceMetric targetMetric _memberRoute sharedPrecision : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CompactUniformContinuityPacket source target graph tolerance precision net coverage modulusRows
        radiusRows fold transport route nameRow bundle pkg →
      UnaryHistory familyMember →
        Cont familyMember net sourceMetric →
          Cont sourceMetric modulusRows targetMetric →
            Cont radiusRows fold sharedPrecision →
              hsame sharedPrecision precision →
                PkgSig bundle targetMetric pkg →
                  UnaryHistory familyMember ∧ UnaryHistory sourceMetric ∧
                    UnaryHistory targetMetric ∧ UnaryHistory sharedPrecision ∧
                      Cont familyMember net sourceMetric ∧
                        Cont sourceMetric modulusRows targetMetric ∧
                          Cont radiusRows fold sharedPrecision ∧
                            hsame sharedPrecision precision ∧
                              PkgSig bundle precision pkg ∧ PkgSig bundle targetMetric pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont UnaryHistory hsame
  intro packet familyUnary memberNetSource sourceModulusTarget radiusFoldShared
    sharedPrecisionSame targetMetricPkg
  obtain ⟨_sourceUnary, _targetUnary, _graphUnary, _toleranceUnary, netUnary,
    coverageUnary, radiusRowsUnary, _transportUnary, _nameRowUnary, netCoverageModulusRows,
    _modulusRowsRadiusRowsFold, _foldTransportRoute, _routeNamePrecision, precisionPkg⟩ :=
      packet
  have modulusRowsUnary : UnaryHistory modulusRows :=
    unary_cont_closed netUnary coverageUnary netCoverageModulusRows
  have foldUnary : UnaryHistory fold :=
    unary_cont_closed modulusRowsUnary radiusRowsUnary _modulusRowsRadiusRowsFold
  have sourceMetricUnary : UnaryHistory sourceMetric :=
    unary_cont_closed familyUnary netUnary memberNetSource
  have targetMetricUnary : UnaryHistory targetMetric :=
    unary_cont_closed sourceMetricUnary modulusRowsUnary sourceModulusTarget
  have sharedPrecisionUnary : UnaryHistory sharedPrecision :=
    unary_cont_closed radiusRowsUnary foldUnary radiusFoldShared
  exact
    ⟨familyUnary, sourceMetricUnary, targetMetricUnary, sharedPrecisionUnary,
      memberNetSource, sourceModulusTarget, radiusFoldShared, sharedPrecisionSame,
      precisionPkg, targetMetricPkg⟩

end BEDC.Derived.CompactUniformContinuityUp
