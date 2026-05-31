import BEDC.Derived.ClosedBoundedIntervalUniformModulusUp.TasteGate
import BEDC.FKernel.Cont
import BEDC.FKernel.Unary

namespace BEDC.Derived.ClosedBoundedIntervalUniformModulusUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Unary

theorem ClosedBoundedIntervalUniformModulusHeineCantorRoute
    {leftEndpoint rightEndpoint intervalRow compactCover dyadicCover lebesgueLedger
      pointwiseModulus uniformOutput transport route provenance name sourceRead centerRead
      outputRead : BHist} :
    UnaryHistory intervalRow ->
      UnaryHistory compactCover ->
        UnaryHistory lebesgueLedger ->
          UnaryHistory pointwiseModulus ->
            Cont intervalRow compactCover sourceRead ->
              Cont sourceRead lebesgueLedger centerRead ->
                Cont centerRead pointwiseModulus outputRead ->
                  closedBoundedIntervalUniformModulusFields
                        (ClosedBoundedIntervalUniformModulusUp.mk leftEndpoint rightEndpoint
                          intervalRow compactCover dyadicCover lebesgueLedger pointwiseModulus
                          uniformOutput transport route provenance name) =
                      [leftEndpoint, rightEndpoint, intervalRow, compactCover, dyadicCover,
                        lebesgueLedger, pointwiseModulus, uniformOutput, transport, route,
                        provenance, name] ∧
                    UnaryHistory sourceRead ∧ UnaryHistory centerRead ∧
                      UnaryHistory outputRead ∧ Cont intervalRow compactCover sourceRead ∧
                        Cont sourceRead lebesgueLedger centerRead ∧
                          Cont centerRead pointwiseModulus outputRead := by
  -- BEDC touchpoint anchor: BHist Cont UnaryHistory
  intro intervalUnary compactUnary lebesgueUnary pointwiseUnary intervalCompactSource
    sourceLebesgueCenter centerPointwiseOutput
  have sourceUnary : UnaryHistory sourceRead :=
    unary_cont_closed intervalUnary compactUnary intervalCompactSource
  have centerUnary : UnaryHistory centerRead :=
    unary_cont_closed sourceUnary lebesgueUnary sourceLebesgueCenter
  have outputUnary : UnaryHistory outputRead :=
    unary_cont_closed centerUnary pointwiseUnary centerPointwiseOutput
  exact
    ⟨rfl, sourceUnary, centerUnary, outputUnary, intervalCompactSource,
      sourceLebesgueCenter, centerPointwiseOutput⟩

theorem ClosedBoundedIntervalUniformModulus_lebesgue_handoff_scope
    {leftEndpoint rightEndpoint intervalRow compactCover dyadicCover lebesgueLedger
      pointwiseModulus uniformOutput transport route provenance name sourceScope outputScope :
        BHist} :
    UnaryHistory dyadicCover →
      UnaryHistory lebesgueLedger →
        UnaryHistory pointwiseModulus →
          Cont dyadicCover lebesgueLedger sourceScope →
            Cont sourceScope pointwiseModulus outputScope →
              closedBoundedIntervalUniformModulusFields
                    (ClosedBoundedIntervalUniformModulusUp.mk leftEndpoint rightEndpoint
                      intervalRow compactCover dyadicCover lebesgueLedger pointwiseModulus
                      uniformOutput transport route provenance name) =
                  [leftEndpoint, rightEndpoint, intervalRow, compactCover, dyadicCover,
                    lebesgueLedger, pointwiseModulus, uniformOutput, transport, route,
                    provenance, name] ∧
                UnaryHistory sourceScope ∧ UnaryHistory outputScope ∧
                  Cont dyadicCover lebesgueLedger sourceScope ∧
                    Cont sourceScope pointwiseModulus outputScope := by
  -- BEDC touchpoint anchor: BHist Cont UnaryHistory
  intro dyadicUnary lebesgueUnary pointwiseUnary dyadicLebesgueSource sourcePointwiseOutput
  have sourceUnary : UnaryHistory sourceScope :=
    unary_cont_closed dyadicUnary lebesgueUnary dyadicLebesgueSource
  have outputUnary : UnaryHistory outputScope :=
    unary_cont_closed sourceUnary pointwiseUnary sourcePointwiseOutput
  exact
    ⟨rfl, sourceUnary, outputUnary, dyadicLebesgueSource, sourcePointwiseOutput⟩

end BEDC.Derived.ClosedBoundedIntervalUniformModulusUp
