import BEDC.Derived.RegularCauchyCriterionUp.TasteGate
import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.RegularCauchyCriterionUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem RegularCauchyCriterionCarrier_tail_transport [AskSetup] [PackageSetup]
    (K : RegularCauchyCriterionUp)
    {S R M D Q V A H C P N streamRead criterionRead realRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    regularCauchyCriterionFields K = [S, R, M, D, Q, V, A, H, C, P, N] →
      UnaryHistory S →
        UnaryHistory R →
          UnaryHistory M →
            UnaryHistory D →
              UnaryHistory Q →
                UnaryHistory V →
                  UnaryHistory A →
                    Cont S R streamRead →
                      Cont M D criterionRead →
                        Cont Q V realRead →
                          PkgSig bundle P pkg →
                            UnaryHistory streamRead ∧ UnaryHistory criterionRead ∧
                              UnaryHistory realRead ∧ Cont S R streamRead ∧
                                Cont M D criterionRead ∧ Cont Q V realRead ∧
                                  PkgSig bundle P pkg := by
  -- BEDC touchpoint anchor: BHist Cont PkgSig UnaryHistory ProbeBundle
  intro fieldRows streamUnary readbackUnary modulusUnary dyadicUnary criterionUnary
    convergenceUnary _realBoundaryUnary streamRoute criterionRoute realRoute provenancePkg
  cases K with
  | mk _stream _readback _modulus _dyadic _criterion _convergence _realBoundary
      _transport _replay _provenance _localName =>
      change
        [_stream, _readback, _modulus, _dyadic, _criterion, _convergence, _realBoundary,
          _transport, _replay, _provenance, _localName] =
          [S, R, M, D, Q, V, A, H, C, P, N] at fieldRows
      have streamReadUnary : UnaryHistory streamRead :=
        unary_cont_closed streamUnary readbackUnary streamRoute
      have criterionReadUnary : UnaryHistory criterionRead :=
        unary_cont_closed modulusUnary dyadicUnary criterionRoute
      have realReadUnary : UnaryHistory realRead :=
        unary_cont_closed criterionUnary convergenceUnary realRoute
      exact
        ⟨streamReadUnary, criterionReadUnary, realReadUnary, streamRoute, criterionRoute,
          realRoute, provenancePkg⟩

end BEDC.Derived.RegularCauchyCriterionUp
