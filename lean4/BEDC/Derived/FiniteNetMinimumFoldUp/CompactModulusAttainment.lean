import BEDC.Derived.FiniteNetMinimumFoldUp

namespace BEDC.Derived.FiniteNetMinimumFoldUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem FiniteNetMinimumFoldPacket_compact_modulus_attainment [AskSetup] [PackageSetup]
    {bundleRow radius accumulator lower transport route provenance nameRow selected exported
      coverRead finalRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    FiniteNetMinimumFoldPacket bundleRow radius accumulator lower transport route provenance
        nameRow bundle pkg →
      Cont accumulator lower selected →
        Cont selected route exported →
          Cont bundleRow radius coverRead →
            Cont exported coverRead finalRead →
              PkgSig bundle selected pkg →
                PkgSig bundle exported pkg →
                  PkgSig bundle finalRead pkg →
                    UnaryHistory selected ∧ UnaryHistory exported ∧
                      UnaryHistory coverRead ∧ UnaryHistory finalRead ∧
                        Cont accumulator lower selected ∧ Cont selected route exported ∧
                          Cont bundleRow radius coverRead ∧ Cont exported coverRead finalRead ∧
                            PkgSig bundle selected pkg ∧ PkgSig bundle exported pkg ∧
                              PkgSig bundle finalRead pkg := by
  -- BEDC touchpoint anchor: BHist UnaryHistory Cont ProbeBundle Pkg
  intro packet accumulatorLowerSelected selectedRouteExported bundleRadiusCover
    exportedCoverFinal selectedPkg exportedPkg finalReadPkg
  obtain ⟨bundleRowUnary, radiusUnary, accumulatorUnary, lowerUnary, nameRowUnary,
    _bundleRadiusAccumulator, accumulatorLowerTransport, transportNameProvenance,
    _bundleRadiusTransport, _transportAccumulatorLower, lowerRouteProvenance,
    _provenancePkg⟩ := packet
  have transportUnary : UnaryHistory transport :=
    unary_cont_closed accumulatorUnary lowerUnary accumulatorLowerTransport
  have provenanceUnary : UnaryHistory provenance :=
    unary_cont_closed transportUnary nameRowUnary transportNameProvenance
  have routeUnary : UnaryHistory route :=
    (unary_cont_factors_from_result lowerRouteProvenance provenanceUnary).right
  have selectedUnary : UnaryHistory selected :=
    unary_cont_closed accumulatorUnary lowerUnary accumulatorLowerSelected
  have exportedUnary : UnaryHistory exported :=
    unary_cont_closed selectedUnary routeUnary selectedRouteExported
  have coverReadUnary : UnaryHistory coverRead :=
    unary_cont_closed bundleRowUnary radiusUnary bundleRadiusCover
  have finalReadUnary : UnaryHistory finalRead :=
    unary_cont_closed exportedUnary coverReadUnary exportedCoverFinal
  exact
    ⟨selectedUnary, exportedUnary, coverReadUnary, finalReadUnary,
      accumulatorLowerSelected, selectedRouteExported, bundleRadiusCover,
      exportedCoverFinal, selectedPkg, exportedPkg, finalReadPkg⟩

end BEDC.Derived.FiniteNetMinimumFoldUp
