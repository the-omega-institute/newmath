import BEDC.Derived.UniformModulusUp

namespace BEDC.Derived.UniformModulusUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem UniformModulusPacket_continuous_map_modulus_lock [AskSetup] [PackageSetup]
    {tolerance precision bundleRow radius coverage pointwise foldLedger transport provenance
      nameRow compactRead pointwiseRead consumer exported : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    UniformModulusPacket tolerance precision bundleRow radius coverage pointwise foldLedger
        transport provenance nameRow bundle pkg ->
      UnaryHistory pointwise ->
        Cont bundleRow radius compactRead ->
          Cont compactRead pointwise pointwiseRead ->
            Cont pointwiseRead transport consumer ->
              Cont consumer nameRow exported ->
                PkgSig bundle exported pkg ->
                  UnaryHistory compactRead ∧ UnaryHistory pointwiseRead ∧
                    UnaryHistory consumer ∧ UnaryHistory exported ∧
                      Cont compactRead pointwise pointwiseRead ∧
                        Cont pointwiseRead transport consumer ∧
                          Cont consumer nameRow exported ∧ PkgSig bundle exported pkg := by
  intro packet pointwiseUnary compactRoute pointwiseRoute consumerRoute exportRoute exportPkg
  obtain ⟨toleranceUnary, _precisionUnary, bundleRowUnary, radiusUnary, nameRowUnary,
    coverageRoute, transportRoute, _precisionRadiusFoldLedger, _foldNameProvenance,
    _provenancePkg⟩ := packet
  have coverageUnary : UnaryHistory coverage :=
    unary_cont_closed toleranceUnary bundleRowUnary coverageRoute
  have transportUnary : UnaryHistory transport :=
    unary_cont_closed coverageUnary pointwiseUnary transportRoute
  have compactReadUnary : UnaryHistory compactRead :=
    unary_cont_closed bundleRowUnary radiusUnary compactRoute
  have pointwiseReadUnary : UnaryHistory pointwiseRead :=
    unary_cont_closed compactReadUnary pointwiseUnary pointwiseRoute
  have consumerUnary : UnaryHistory consumer :=
    unary_cont_closed pointwiseReadUnary transportUnary consumerRoute
  have exportedUnary : UnaryHistory exported :=
    unary_cont_closed consumerUnary nameRowUnary exportRoute
  exact
    ⟨compactReadUnary, pointwiseReadUnary, consumerUnary, exportedUnary, pointwiseRoute,
      consumerRoute, exportRoute, exportPkg⟩

end BEDC.Derived.UniformModulusUp
