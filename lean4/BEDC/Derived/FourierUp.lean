import BEDC.FKernel.Sig

namespace BEDC.Derived.FourierUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Ext
open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.FKernel.Sig

theorem FourierFiniteObservation_carrier_obligation [AskSetup]
    {bundle : ProbeBundle ProbeName} {source observed : BHist} :
    SigRel bundle source observed ->
      (bundle = ProbeBundle.Bnil ∧ hsame observed BHist.Empty) ∨
        ∃ pi : ProbeName, ∃ tail : ProbeBundle ProbeName, ∃ obsPrefix : BHist,
          ∃ mark : BMark, ∃ evidence : Evidence,
            bundle = ProbeBundle.Bcons pi tail ∧
              Ask pi source mark evidence ∧
                SigRel tail source obsPrefix ∧ Ext obsPrefix mark observed := by
  intro observedRow
  cases observedRow with
  | empty h =>
      exact Or.inl (And.intro rfl (hsame_refl BHist.Empty))
  | cons pi tail h obsPrefix r mark evidence askRow tailRow extRow =>
      exact Or.inr
        (Exists.intro pi
          (Exists.intro tail
            (Exists.intro obsPrefix
              (Exists.intro mark
                (Exists.intro evidence
                  (And.intro rfl
                    (And.intro askRow (And.intro tailRow extRow))))))))

theorem FourierFiniteObservation_policy_singleton_observation [AskSetup] {D : BHist -> Prop}
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
