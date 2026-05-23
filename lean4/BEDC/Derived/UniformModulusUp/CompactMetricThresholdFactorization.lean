import BEDC.Derived.UniformModulusUp

namespace BEDC.Derived.UniformModulusUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem UniformModulusPacket_compact_metric_threshold_factorization [AskSetup] [PackageSetup]
    {tolerance precision bundleRow radius coverage pointwise foldLedger transport provenance
      nameRow compactRead pointwiseRead distance exported : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    UniformModulusPacket tolerance precision bundleRow radius coverage pointwise foldLedger
        transport provenance nameRow bundle pkg ->
      UnaryHistory pointwise ->
        Cont bundleRow radius compactRead ->
          Cont compactRead pointwise pointwiseRead ->
            Cont pointwiseRead foldLedger distance ->
              Cont distance nameRow exported ->
                PkgSig bundle exported pkg ->
                  UnaryHistory bundleRow ∧ UnaryHistory radius ∧ UnaryHistory compactRead ∧
                    UnaryHistory pointwiseRead ∧ UnaryHistory foldLedger ∧
                      UnaryHistory distance ∧ UnaryHistory exported ∧
                        Cont bundleRow radius compactRead ∧
                          Cont compactRead pointwise pointwiseRead ∧
                            Cont pointwiseRead foldLedger distance ∧
                              Cont distance nameRow exported ∧ PkgSig bundle exported pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont UnaryHistory PkgSig
  intro packet pointwiseUnary compactRoute pointwiseRoute distanceRoute exportRoute exportPkg
  obtain ⟨_toleranceUnary, precisionUnary, bundleRowUnary, radiusUnary, nameRowUnary,
    _coverageRoute, _transportRoute, precisionRadiusFoldLedger, _foldNameProvenance,
    _provenancePkg⟩ := packet
  have compactReadUnary : UnaryHistory compactRead :=
    unary_cont_closed bundleRowUnary radiusUnary compactRoute
  have pointwiseReadUnary : UnaryHistory pointwiseRead :=
    unary_cont_closed compactReadUnary pointwiseUnary pointwiseRoute
  have foldLedgerUnary : UnaryHistory foldLedger :=
    unary_cont_closed precisionUnary radiusUnary precisionRadiusFoldLedger
  have distanceUnary : UnaryHistory distance :=
    unary_cont_closed pointwiseReadUnary foldLedgerUnary distanceRoute
  have exportedUnary : UnaryHistory exported :=
    unary_cont_closed distanceUnary nameRowUnary exportRoute
  exact
    ⟨bundleRowUnary, radiusUnary, compactReadUnary, pointwiseReadUnary, foldLedgerUnary,
      distanceUnary, exportedUnary, compactRoute, pointwiseRoute, distanceRoute, exportRoute,
      exportPkg⟩

end BEDC.Derived.UniformModulusUp
