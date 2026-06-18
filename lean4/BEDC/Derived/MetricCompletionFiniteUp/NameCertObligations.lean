import BEDC.Derived.MetricCompletionFiniteUp.TasteGate
import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.MetricCompletionFiniteUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem MetricCompletionFiniteCarrier_obligation_boundary [AskSetup] [PackageSetup]
    (F : MetricCompletionFiniteUp) {M B W E R S H C P N sourceRead readback : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    metricCompletionFiniteFields F = [M, B, W, E, R, S, H, C, P, N] →
      UnaryHistory M →
        UnaryHistory B →
          UnaryHistory W →
            UnaryHistory E →
              UnaryHistory S →
                Cont M B sourceRead →
                  Cont W E readback →
                    PkgSig bundle P pkg →
                      UnaryHistory sourceRead ∧ UnaryHistory readback ∧
                        Cont M B sourceRead ∧ Cont W E readback ∧
                          PkgSig bundle P pkg := by
  -- BEDC touchpoint anchor: BHist Cont PkgSig UnaryHistory ProbeBundle
  intro fieldRows metricUnary basisUnary windowUnary embeddingUnary _selectorUnary
    sourceRoute readbackRoute provenancePkg
  cases F with
  | mk _metric _basis _window _embedding _readback _selector _transport _replay
      _provenance _localName =>
      change
        [_metric, _basis, _window, _embedding, _readback, _selector, _transport,
          _replay, _provenance, _localName] =
          [M, B, W, E, R, S, H, C, P, N] at fieldRows
      have sourceUnary : UnaryHistory sourceRead :=
        unary_cont_closed metricUnary basisUnary sourceRoute
      have readbackUnary : UnaryHistory readback :=
        unary_cont_closed windowUnary embeddingUnary readbackRoute
      exact
        ⟨sourceUnary, readbackUnary, sourceRoute, readbackRoute, provenancePkg⟩

end BEDC.Derived.MetricCompletionFiniteUp
