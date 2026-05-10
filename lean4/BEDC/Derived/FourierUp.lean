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

theorem FourierFiniteObservation_ledger_obligation [AskSetup]
    {D : BHist -> Prop} (policy : AskPolicy D) {pi : ProbeName} {h : BHist} :
    D h -> exists bundle : ProbeBundle ProbeName, exists r : BHist, exists m : BMark,
      exists delta : Evidence,
        InBundle pi bundle ∧ Ask pi h m delta ∧ SigRel bundle h r := by
  intro carrierH
  cases policy.total (π := pi) (h := h) carrierH with
  | intro mark markData =>
      cases markData with
      | intro delta askRow =>
          cases mark with
          | b0 =>
              exact Exists.intro (ProbeBundle.Bcons pi ProbeBundle.Bnil)
                (Exists.intro (BHist.e0 BHist.Empty)
                  (Exists.intro BMark.b0
                    (Exists.intro delta
                      (And.intro (Or.inl rfl)
                        (And.intro askRow
                          (SigRel.cons pi ProbeBundle.Bnil h BHist.Empty
                            (BHist.e0 BHist.Empty) BMark.b0 delta askRow
                            (SigRel.empty h) (Ext.e0 BHist.Empty)))))))
          | b1 =>
              exact Exists.intro (ProbeBundle.Bcons pi ProbeBundle.Bnil)
                (Exists.intro (BHist.e1 BHist.Empty)
                  (Exists.intro BMark.b1
                    (Exists.intro delta
                      (And.intro (Or.inl rfl)
                        (And.intro askRow
                          (SigRel.cons pi ProbeBundle.Bnil h BHist.Empty
                            (BHist.e1 BHist.Empty) BMark.b1 delta askRow
                            (SigRel.empty h) (Ext.e1 BHist.Empty)))))))

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

theorem FourierFiniteObservation_exactness_obligation [AskSetup]
    {D : BHist -> Prop} (policy : AskPolicy D) {bundle : ProbeBundle ProbeName}
    {h k s t : BHist} :
    D h -> D k -> SigRel bundle h s -> SigRel bundle k t -> SameSig bundle h k ->
      hsame s t := by
  intro carrierH carrierK sigH sigK sameSigHK
  cases sameSigHK with
  | intro s0 sameSigTail =>
      cases sameSigTail with
      | intro t0 sameSigData =>
          cases sameSigData with
          | intro sigH0 sameSigRest =>
              cases sameSigRest with
              | intro sigK0 sameS0T0 =>
                  have sameSS0 : hsame s s0 :=
                    sig_deterministic
                      (bundle := bundle)
                      (D := D)
                      (h := h)
                      (s := s)
                      (t := s0)
                      policy
                      carrierH
                      sigH
                      sigH0
                  have sameT0T : hsame t0 t :=
                    sig_deterministic
                      (bundle := bundle)
                      (D := D)
                      (h := k)
                      (s := t0)
                      (t := t)
                      policy
                      carrierK
                      sigK0
                      sigK
                  exact hsame_trans sameSS0 (hsame_trans sameS0T0 sameT0T)

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

theorem FourierFiniteObservation_standard_bridge [AskSetup]
    {D : BHist -> Prop} (policy : AskPolicy D) {pi : ProbeName} {h k : BHist} :
    D h -> D k -> hsame h k ->
      exists s : BHist, exists t : BHist,
        SigRel (ProbeBundle.Bcons pi ProbeBundle.Bnil) h s ∧
          SigRel (ProbeBundle.Bcons pi ProbeBundle.Bnil) k t ∧
            SameSig (ProbeBundle.Bcons pi ProbeBundle.Bnil) h k ∧ hsame s t := by
  intro carrierH carrierK sameHK
  cases policy.total (π := pi) (h := h) carrierH with
  | intro markH markHData =>
      cases markHData with
      | intro deltaH askH =>
          cases policy.total (π := pi) (h := k) carrierK with
          | intro markK markKData =>
              cases markKData with
              | intro deltaK askK =>
                  cases markH with
                  | b0 =>
                      cases markK with
                      | b0 =>
                          let s := BHist.e0 BHist.Empty
                          let t := BHist.e0 BHist.Empty
                          have sigH :
                              SigRel (ProbeBundle.Bcons pi ProbeBundle.Bnil) h s :=
                            SigRel.cons pi ProbeBundle.Bnil h BHist.Empty s
                              BMark.b0 deltaH askH (SigRel.empty h) (Ext.e0 BHist.Empty)
                          have sigK :
                              SigRel (ProbeBundle.Bcons pi ProbeBundle.Bnil) k t :=
                            SigRel.cons pi ProbeBundle.Bnil k BHist.Empty t
                              BMark.b0 deltaK askK (SigRel.empty k) (Ext.e0 BHist.Empty)
                          have classified :=
                            FourierFiniteObservation_classifier_obligation
                              (D := D)
                              (bundle := ProbeBundle.Bcons pi ProbeBundle.Bnil)
                              (h := h)
                              (k := k)
                              (s := s)
                              (t := t)
                              policy
                              carrierH
                              carrierK
                              sameHK
                              sigH
                              sigK
                          exact Exists.intro s
                            (Exists.intro t
                              (And.intro sigH (And.intro sigK classified)))
                      | b1 =>
                          let s := BHist.e0 BHist.Empty
                          let t := BHist.e1 BHist.Empty
                          have sigH :
                              SigRel (ProbeBundle.Bcons pi ProbeBundle.Bnil) h s :=
                            SigRel.cons pi ProbeBundle.Bnil h BHist.Empty s
                              BMark.b0 deltaH askH (SigRel.empty h) (Ext.e0 BHist.Empty)
                          have sigK :
                              SigRel (ProbeBundle.Bcons pi ProbeBundle.Bnil) k t :=
                            SigRel.cons pi ProbeBundle.Bnil k BHist.Empty t
                              BMark.b1 deltaK askK (SigRel.empty k) (Ext.e1 BHist.Empty)
                          have classified :=
                            FourierFiniteObservation_classifier_obligation
                              (D := D)
                              (bundle := ProbeBundle.Bcons pi ProbeBundle.Bnil)
                              (h := h)
                              (k := k)
                              (s := s)
                              (t := t)
                              policy
                              carrierH
                              carrierK
                              sameHK
                              sigH
                              sigK
                          exact Exists.intro s
                            (Exists.intro t
                              (And.intro sigH (And.intro sigK classified)))
                  | b1 =>
                      cases markK with
                      | b0 =>
                          let s := BHist.e1 BHist.Empty
                          let t := BHist.e0 BHist.Empty
                          have sigH :
                              SigRel (ProbeBundle.Bcons pi ProbeBundle.Bnil) h s :=
                            SigRel.cons pi ProbeBundle.Bnil h BHist.Empty s
                              BMark.b1 deltaH askH (SigRel.empty h) (Ext.e1 BHist.Empty)
                          have sigK :
                              SigRel (ProbeBundle.Bcons pi ProbeBundle.Bnil) k t :=
                            SigRel.cons pi ProbeBundle.Bnil k BHist.Empty t
                              BMark.b0 deltaK askK (SigRel.empty k) (Ext.e0 BHist.Empty)
                          have classified :=
                            FourierFiniteObservation_classifier_obligation
                              (D := D)
                              (bundle := ProbeBundle.Bcons pi ProbeBundle.Bnil)
                              (h := h)
                              (k := k)
                              (s := s)
                              (t := t)
                              policy
                              carrierH
                              carrierK
                              sameHK
                              sigH
                              sigK
                          exact Exists.intro s
                            (Exists.intro t
                              (And.intro sigH (And.intro sigK classified)))
                      | b1 =>
                          let s := BHist.e1 BHist.Empty
                          let t := BHist.e1 BHist.Empty
                          have sigH :
                              SigRel (ProbeBundle.Bcons pi ProbeBundle.Bnil) h s :=
                            SigRel.cons pi ProbeBundle.Bnil h BHist.Empty s
                              BMark.b1 deltaH askH (SigRel.empty h) (Ext.e1 BHist.Empty)
                          have sigK :
                              SigRel (ProbeBundle.Bcons pi ProbeBundle.Bnil) k t :=
                            SigRel.cons pi ProbeBundle.Bnil k BHist.Empty t
                              BMark.b1 deltaK askK (SigRel.empty k) (Ext.e1 BHist.Empty)
                          have classified :=
                            FourierFiniteObservation_classifier_obligation
                              (D := D)
                              (bundle := ProbeBundle.Bcons pi ProbeBundle.Bnil)
                              (h := h)
                              (k := k)
                              (s := s)
                              (t := t)
                              policy
                              carrierH
                              carrierK
                              sameHK
                              sigH
                              sigK
                          exact Exists.intro s
                            (Exists.intro t
                              (And.intro sigH (And.intro sigK classified)))

end BEDC.Derived.FourierUp
