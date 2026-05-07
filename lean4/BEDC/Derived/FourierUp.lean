import BEDC.FKernel.Sig

namespace BEDC.Derived.FourierUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Ext
open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.FKernel.Sig

theorem FourierFiniteObservation_carrier_obligation [AskSetup] {D : BHist -> Prop}
    (policy : AskPolicy D) {pi : ProbeName} {h : BHist} :
    D h -> exists bundle : ProbeBundle ProbeName, exists r : BHist,
      InBundle pi bundle ∧ SigRel bundle h r := by
  intro carrierH
  cases policy.total (π := pi) (h := h) carrierH with
  | intro mark markData =>
      cases markData with
      | intro delta askRow =>
          cases mark with
          | b0 =>
              exact Exists.intro (ProbeBundle.Bcons pi ProbeBundle.Bnil)
                (Exists.intro (BHist.e0 BHist.Empty)
                  (And.intro (Or.inl rfl)
                    (SigRel.cons pi ProbeBundle.Bnil h BHist.Empty (BHist.e0 BHist.Empty)
                      BMark.b0 delta askRow (SigRel.empty h) (Ext.e0 BHist.Empty))))
          | b1 =>
              exact Exists.intro (ProbeBundle.Bcons pi ProbeBundle.Bnil)
                (Exists.intro (BHist.e1 BHist.Empty)
                  (And.intro (Or.inl rfl)
                    (SigRel.cons pi ProbeBundle.Bnil h BHist.Empty (BHist.e1 BHist.Empty)
                      BMark.b1 delta askRow (SigRel.empty h) (Ext.e1 BHist.Empty))))

end BEDC.Derived.FourierUp
