import BEDC.Derived.CompactUniformContinuityUp

namespace BEDC.Derived.CompactUniformContinuityUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem CompactUniformContinuityPacket_kernel_net_observation_surface [AskSetup]
    [PackageSetup]
    {source target graph tolerance precision net coverage modulusRows radiusRows fold transport
      route nameRow sourceRead targetRead radiusRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CompactUniformContinuityPacket source target graph tolerance precision net coverage
        modulusRows radiusRows fold transport route nameRow bundle pkg ->
      Cont source coverage sourceRead ->
        Cont target modulusRows targetRead ->
          Cont radiusRows fold radiusRead ->
            PkgSig bundle sourceRead pkg ->
              PkgSig bundle targetRead pkg ->
                PkgSig bundle radiusRead pkg ->
                  UnaryHistory source ∧ UnaryHistory target ∧ UnaryHistory net ∧
                    UnaryHistory coverage ∧ UnaryHistory modulusRows ∧
                      UnaryHistory radiusRows ∧ UnaryHistory fold ∧
                        UnaryHistory precision ∧ UnaryHistory sourceRead ∧
                          UnaryHistory targetRead ∧ UnaryHistory radiusRead ∧
                            Cont net coverage modulusRows ∧
                              Cont modulusRows radiusRows fold ∧
                                Cont fold transport route ∧ Cont route nameRow precision ∧
                                  Cont source coverage sourceRead ∧
                                    Cont target modulusRows targetRead ∧
                                      Cont radiusRows fold radiusRead ∧
                                        PkgSig bundle precision pkg ∧
                                          PkgSig bundle sourceRead pkg ∧
                                            PkgSig bundle targetRead pkg ∧
                                              PkgSig bundle radiusRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont UnaryHistory
  intro packet sourceCoverageRead targetModulusRead radiusFoldRead sourceReadPkg targetReadPkg
    radiusReadPkg
  obtain ⟨sourceUnary, targetUnary, _graphUnary, _toleranceUnary, netUnary,
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
  have sourceReadUnary : UnaryHistory sourceRead :=
    unary_cont_closed sourceUnary coverageUnary sourceCoverageRead
  have targetReadUnary : UnaryHistory targetRead :=
    unary_cont_closed targetUnary modulusRowsUnary targetModulusRead
  have radiusReadUnary : UnaryHistory radiusRead :=
    unary_cont_closed radiusRowsUnary foldUnary radiusFoldRead
  exact
    ⟨sourceUnary, targetUnary, netUnary, coverageUnary, modulusRowsUnary,
      radiusRowsUnary, foldUnary, precisionUnary, sourceReadUnary, targetReadUnary,
      radiusReadUnary, netCoverageModulusRows, modulusRowsRadiusRowsFold,
      foldTransportRoute, routeNamePrecision, sourceCoverageRead, targetModulusRead,
      radiusFoldRead, precisionPkg, sourceReadPkg, targetReadPkg, radiusReadPkg⟩

end BEDC.Derived.CompactUniformContinuityUp
