import BEDC.Derived.CompactUniformContinuityUp

namespace BEDC.Derived.CompactUniformContinuityUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem CompactUniformContinuityPacket_finite_net_modulus_extraction [AskSetup]
    [PackageSetup]
    {source target graph tolerance precision net coverage modulusRows radiusRows fold transport
      route nameRow centerRead radiusRead foldedPrecision : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CompactUniformContinuityPacket source target graph tolerance precision net coverage
        modulusRows radiusRows fold transport route nameRow bundle pkg ->
      Cont net coverage centerRead ->
        Cont centerRead radiusRows radiusRead ->
          Cont radiusRows fold foldedPrecision ->
            hsame foldedPrecision precision ->
              PkgSig bundle centerRead pkg ->
                PkgSig bundle radiusRead pkg ->
                  PkgSig bundle foldedPrecision pkg ->
                    UnaryHistory net ∧ UnaryHistory coverage ∧ UnaryHistory centerRead ∧
                      UnaryHistory radiusRows ∧ UnaryHistory radiusRead ∧ UnaryHistory fold ∧
                        UnaryHistory foldedPrecision ∧ UnaryHistory precision ∧
                          Cont net coverage centerRead ∧
                            Cont centerRead radiusRows radiusRead ∧
                              Cont radiusRows fold foldedPrecision ∧
                                hsame foldedPrecision precision ∧
                                  PkgSig bundle precision pkg ∧
                                    PkgSig bundle centerRead pkg ∧
                                      PkgSig bundle radiusRead pkg ∧
                                        PkgSig bundle foldedPrecision pkg := by
  -- BEDC touchpoint anchor: BHist Cont Pkg ProbeBundle hsame
  intro packet netCoverageCenter centerRadiusRead radiusFoldPrecision samePrecision
    centerPkg radiusPkg foldedPkg
  obtain ⟨_sourceUnary, _targetUnary, _graphUnary, _toleranceUnary, netUnary,
    coverageUnary, radiusRowsUnary, _transportUnary, _nameRowUnary, netCoverageModulusRows,
    modulusRowsRadiusRowsFold, _foldTransportRoute, _routeNamePrecision, precisionPkg⟩ :=
      packet
  have centerUnary : UnaryHistory centerRead :=
    unary_cont_closed netUnary coverageUnary netCoverageCenter
  have radiusReadUnary : UnaryHistory radiusRead :=
    unary_cont_closed centerUnary radiusRowsUnary centerRadiusRead
  have modulusRowsUnary : UnaryHistory modulusRows :=
    unary_cont_closed netUnary coverageUnary netCoverageModulusRows
  have foldUnary : UnaryHistory fold :=
    unary_cont_closed modulusRowsUnary radiusRowsUnary modulusRowsRadiusRowsFold
  have foldedPrecisionUnary : UnaryHistory foldedPrecision :=
    unary_cont_closed radiusRowsUnary foldUnary radiusFoldPrecision
  have precisionUnary : UnaryHistory precision := by
    cases samePrecision
    exact foldedPrecisionUnary
  exact
    ⟨netUnary, coverageUnary, centerUnary, radiusRowsUnary, radiusReadUnary, foldUnary,
      foldedPrecisionUnary, precisionUnary, netCoverageCenter, centerRadiusRead,
      radiusFoldPrecision, samePrecision, precisionPkg, centerPkg, radiusPkg, foldedPkg⟩

end BEDC.Derived.CompactUniformContinuityUp
