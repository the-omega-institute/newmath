import BEDC.Derived.CompactMetricUp
import BEDC.FKernel.Ask
import BEDC.FKernel.Package

namespace BEDC.Derived.CompactMetricUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem CompactMetricCarrier_uniform_window_consumer_route [AskSetup] [PackageSetup]
    {space finiteNet radius modulus window consumer provenance : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    UnaryHistory space ->
      UnaryHistory finiteNet ->
        UnaryHistory radius ->
          Cont space radius window ->
            Cont window finiteNet modulus ->
              Cont modulus radius consumer ->
                PkgSig bundle provenance pkg ->
                  UnaryHistory window ∧ UnaryHistory modulus ∧ UnaryHistory consumer ∧
                    hsame window (append space radius) ∧
                      hsame modulus (append window finiteNet) ∧
                        hsame consumer (append modulus radius) ∧ Cont space radius window ∧
                          Cont window finiteNet modulus ∧ Cont modulus radius consumer ∧
                            PkgSig bundle provenance pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig hsame UnaryHistory append
  intro spaceUnary finiteNetUnary radiusUnary windowRoute modulusRoute consumerRoute
    provenancePkg
  have windowUnary : UnaryHistory window :=
    unary_cont_closed spaceUnary radiusUnary windowRoute
  have modulusUnary : UnaryHistory modulus :=
    unary_cont_closed windowUnary finiteNetUnary modulusRoute
  have consumerUnary : UnaryHistory consumer :=
    unary_cont_closed modulusUnary radiusUnary consumerRoute
  have windowExact : hsame window (append space radius) := by
    cases windowRoute
    exact hsame_refl _
  have modulusExact : hsame modulus (append window finiteNet) := by
    cases modulusRoute
    exact hsame_refl _
  have consumerExact : hsame consumer (append modulus radius) := by
    cases consumerRoute
    exact hsame_refl _
  exact
    ⟨windowUnary, modulusUnary, consumerUnary, windowExact, modulusExact, consumerExact,
      windowRoute, modulusRoute, consumerRoute, provenancePkg⟩

end BEDC.Derived.CompactMetricUp
