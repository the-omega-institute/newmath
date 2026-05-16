import BEDC.Derived.CompactUniformContinuityUp

namespace BEDC.Derived.CompactUniformContinuityUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem CompactUniformContinuityPacket_modulus_choice_surface [AskSetup] [PackageSetup]
    {source target graph tolerance precision net coverage modulusRows radiusRows fold transport
      route nameRow centerRead radiusRead pointwiseRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CompactUniformContinuityPacket source target graph tolerance precision net coverage
        modulusRows radiusRows fold transport route nameRow bundle pkg ->
      Cont net coverage centerRead ->
        Cont radiusRows fold radiusRead ->
          Cont centerRead modulusRows pointwiseRead ->
            PkgSig bundle pointwiseRead pkg ->
              UnaryHistory precision ∧ UnaryHistory centerRead ∧ UnaryHistory radiusRead ∧
                UnaryHistory pointwiseRead ∧ Cont net coverage modulusRows ∧
                  Cont modulusRows radiusRows fold ∧ Cont fold transport route ∧
                    Cont route nameRow precision ∧ Cont net coverage centerRead ∧
                      Cont radiusRows fold radiusRead ∧
                        Cont centerRead modulusRows pointwiseRead ∧
                          PkgSig bundle precision pkg ∧ PkgSig bundle pointwiseRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont UnaryHistory
  intro packet netCoverageCenter radiusRowsFoldRadius centerModulusPointwise pointwisePkg
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
  have centerUnary : UnaryHistory centerRead :=
    unary_cont_closed netUnary coverageUnary netCoverageCenter
  have radiusReadUnary : UnaryHistory radiusRead :=
    unary_cont_closed radiusRowsUnary foldUnary radiusRowsFoldRadius
  have pointwiseUnary : UnaryHistory pointwiseRead :=
    unary_cont_closed centerUnary modulusRowsUnary centerModulusPointwise
  exact
    ⟨precisionUnary, centerUnary, radiusReadUnary, pointwiseUnary, netCoverageModulusRows,
      modulusRowsRadiusRowsFold, foldTransportRoute, routeNamePrecision, netCoverageCenter,
      radiusRowsFoldRadius, centerModulusPointwise, precisionPkg, pointwisePkg⟩

end BEDC.Derived.CompactUniformContinuityUp
