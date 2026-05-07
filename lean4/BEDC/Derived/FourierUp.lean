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

theorem FourierFiniteObservation_classifier_obligation [AskSetup]
    {D : BHist -> Prop} (policy : AskPolicy D) {bundle : ProbeBundle ProbeName}
    {h k s t : BHist} :
    D h -> D k -> hsame h k -> SigRel bundle h s -> SigRel bundle k t ->
      SameSig bundle h k ∧ hsame s t := by
  intro _carrierH _carrierK sameHK sigH sigK
  have sameST : hsame s t :=
    sig_respects_history
      (bundle := bundle)
      (D := D)
      (h := h)
      (k := k)
      (s := s)
      (t := t)
      policy
      sameHK
      sigH
      sigK
  exact And.intro (sameSig_intro_from_witnesses sigH sigK sameST) sameST

theorem FourierFiniteObservation_stability_obligation [AskSetup]
    {D : BHist -> Prop} (policy : AskPolicy D) {bundle : ProbeBundle ProbeName}
    {h h' k k' s t : BHist} :
    D h -> D h' -> D k -> D k' -> hsame h k -> hsame h h' -> hsame k k' ->
      SigRel bundle h s -> SigRel bundle k t ->
        exists s' : BHist, exists t' : BHist,
          SigRel bundle h' s' ∧ SigRel bundle k' t' ∧ hsame s s' ∧ hsame t t' ∧
            SameSig bundle h' k' := by
  intro _carrierH carrierH' _carrierK carrierK' sameHK sameHH' sameKK' sigH sigK
  cases sig_total_from_policy
      (bundle := bundle)
      (D := D)
      (h := h')
      policy
      carrierH' with
  | intro s' sigH' =>
      cases sig_total_from_policy
          (bundle := bundle)
          (D := D)
          (h := k')
          policy
          carrierK' with
      | intro t' sigK' =>
          have sameSS' : hsame s s' :=
            sig_respects_history
              (bundle := bundle)
              (D := D)
              (h := h)
              (k := h')
              (s := s)
              (t := s')
              policy
              sameHH'
              sigH
              sigH'
          have sameTT' : hsame t t' :=
            sig_respects_history
              (bundle := bundle)
              (D := D)
              (h := k)
              (k := k')
              (s := t)
              (t := t')
              policy
              sameKK'
              sigK
              sigK'
          have sameH'K' : hsame h' k' :=
            hsame_trans (hsame_trans (hsame_symm sameHH') sameHK) sameKK'
          have sameSigH'K' : SameSig bundle h' k' :=
            sameSig_intro_from_witnesses
              sigH'
              sigK'
              (sig_respects_history
                (bundle := bundle)
                (D := D)
                (h := h')
                (k := k')
                (s := s')
                (t := t')
                policy
                sameH'K'
                sigH'
                sigK')
          exact Exists.intro s'
            (Exists.intro t'
              (And.intro sigH'
                (And.intro sigK'
                  (And.intro sameSS'
                    (And.intro sameTT' sameSigH'K')))))

end BEDC.Derived.FourierUp
