import BEDC.Derived.SubordinateModulusCoverUp.TasteGate
import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.SubordinateModulusCoverUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem SubordinateModulusCoverRationalSubordinationExactness [AskSetup] [PackageSetup]
    {E bundleSpine centers radii precision pointwise coverage comparisons transport route
      provenance name comparisonRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    SubordinateModulusCoverCarrier E bundleSpine centers radii precision pointwise coverage
        comparisons transport route provenance name bundle pkg →
      Cont radii precision comparisonRead →
        PkgSig bundle comparisonRead pkg →
          UnaryHistory radii ∧ UnaryHistory precision ∧ UnaryHistory comparisons ∧
            UnaryHistory comparisonRead ∧ Cont radii precision comparisons ∧
              Cont radii precision comparisonRead ∧ PkgSig bundle provenance pkg ∧
                PkgSig bundle name pkg ∧ PkgSig bundle comparisonRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig UnaryHistory
  intro carrier radiiPrecisionRead comparisonReadPkg
  obtain ⟨_eUnary, _bundleUnary, _centersUnary, radiiUnary, precisionUnary,
    _pointwiseUnary, _coverageUnary, comparisonsUnary, _transportUnary, _routeUnary,
    _provenanceUnary, _nameUnary, _coverageRoute, comparisonRoute, provenancePkg,
    namePkg⟩ := carrier
  have comparisonReadUnary : UnaryHistory comparisonRead :=
    unary_cont_closed radiiUnary precisionUnary radiiPrecisionRead
  exact
    ⟨radiiUnary, precisionUnary, comparisonsUnary, comparisonReadUnary, comparisonRoute,
      radiiPrecisionRead, provenancePkg, namePkg, comparisonReadPkg⟩

theorem SubordinateModulusCoverLedgerExactness [AskSetup] [PackageSetup]
    {E bundleSpine centers radii precision pointwise coverage comparisons transport route
      provenance name coverageRead pointwiseRead comparisonRead uniformRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    SubordinateModulusCoverCarrier E bundleSpine centers radii precision pointwise coverage
        comparisons transport route provenance name bundle pkg →
      Cont centers coverage coverageRead →
        Cont centers pointwise pointwiseRead →
          Cont radii precision comparisonRead →
            Cont comparisonRead route uniformRead →
              PkgSig bundle coverageRead pkg →
                PkgSig bundle pointwiseRead pkg →
                  PkgSig bundle comparisonRead pkg →
                    PkgSig bundle uniformRead pkg →
                      UnaryHistory bundleSpine ∧ UnaryHistory centers ∧
                        UnaryHistory radii ∧ UnaryHistory precision ∧
                          UnaryHistory coverageRead ∧ UnaryHistory pointwiseRead ∧
                            UnaryHistory comparisonRead ∧ UnaryHistory uniformRead ∧
                              Cont centers coverage coverageRead ∧
                                Cont centers pointwise pointwiseRead ∧
                                  Cont radii precision comparisonRead ∧
                                    Cont comparisonRead route uniformRead ∧
                                      PkgSig bundle provenance pkg ∧
                                        PkgSig bundle name pkg ∧
                                          PkgSig bundle uniformRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig UnaryHistory
  intro carrier centersCoverageRead centersPointwiseRead radiiPrecisionRead
    comparisonRouteRead _coverageReadPkg _pointwiseReadPkg _comparisonReadPkg uniformReadPkg
  obtain ⟨_eUnary, bundleSpineUnary, centersUnary, radiiUnary, precisionUnary,
    pointwiseUnary, coverageUnary, _comparisonsUnary, _transportUnary, routeUnary,
    _provenanceUnary, _nameUnary, _coverageRoute, _comparisonRoute, provenancePkg,
    namePkg⟩ := carrier
  have coverageReadUnary : UnaryHistory coverageRead :=
    unary_cont_closed centersUnary coverageUnary centersCoverageRead
  have pointwiseReadUnary : UnaryHistory pointwiseRead :=
    unary_cont_closed centersUnary pointwiseUnary centersPointwiseRead
  have comparisonReadUnary : UnaryHistory comparisonRead :=
    unary_cont_closed radiiUnary precisionUnary radiiPrecisionRead
  have uniformReadUnary : UnaryHistory uniformRead :=
    unary_cont_closed comparisonReadUnary routeUnary comparisonRouteRead
  exact
    ⟨bundleSpineUnary, centersUnary, radiiUnary, precisionUnary, coverageReadUnary,
      pointwiseReadUnary, comparisonReadUnary, uniformReadUnary, centersCoverageRead,
      centersPointwiseRead, radiiPrecisionRead, comparisonRouteRead, provenancePkg, namePkg,
      uniformReadPkg⟩

end BEDC.Derived.SubordinateModulusCoverUp
