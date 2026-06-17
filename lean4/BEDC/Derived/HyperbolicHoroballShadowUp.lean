import BEDC.Derived.HyperbolicHoroballShadowUp.TasteGate
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.Unary

namespace BEDC.Derived.HyperbolicHoroballShadowUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Unary

def HyperbolicHoroballShadowCarrier (B V M O S R E H C P _N : BHist) : Prop :=
  UnaryHistory B ∧ UnaryHistory V ∧ UnaryHistory M ∧ UnaryHistory O ∧
    UnaryHistory S ∧ UnaryHistory R ∧ UnaryHistory E ∧ Cont B V M ∧ Cont M O S ∧
      Cont S R E ∧ Cont H C P

theorem HyperbolicHoroballShadowCarrier_row_exposure
    {B V M O S R E H C P N : BHist} :
    HyperbolicHoroballShadowCarrier B V M O S R E H C P N →
      UnaryHistory B ∧ UnaryHistory S ∧ UnaryHistory E ∧ Cont B V M ∧
        Cont M O S ∧ Cont S R E ∧ Cont H C P := by
  -- BEDC touchpoint anchor: BHist Cont UnaryHistory
  intro carrier
  obtain
    ⟨busemannUnary, _visualUnary, _metricUnary, _observerUnary, shadowUnary,
      _refusalUnary, sealUnary, busemannVisualMetric, metricObserverShadow,
      shadowRefusalSeal, transportReplay⟩ := carrier
  exact
    ⟨busemannUnary, shadowUnary, sealUnary, busemannVisualMetric, metricObserverShadow,
      shadowRefusalSeal, transportReplay⟩

end BEDC.Derived.HyperbolicHoroballShadowUp
