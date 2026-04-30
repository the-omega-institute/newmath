import BEDC.FKernel.Ext
import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle

/-! Signature generation compresses asking events into internal answer histories. -/
namespace BEDC.FKernel.Sig

open BEDC.FKernel.Mark
open BEDC.FKernel.Hist
open BEDC.FKernel.Ext
open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle

variable [AskSetup]

inductive SigRel : ProbeBundle ProbeName → BHist → BHist → Prop where
  | empty (h : BHist) : SigRel (ProbeBundle.Bnil : ProbeBundle ProbeName) h BHist.Empty
  | cons (pi : ProbeName) (tail : ProbeBundle ProbeName) (h s r : BHist) (m : BMark) (delta : Evidence) :
      Ask pi h m delta →
      SigRel tail h s →
      Ext s m r →
      SigRel (ProbeBundle.Bcons pi tail) h r

theorem sig_empty_constructor [AskSetup] (h : BHist) :
    SigRel (ProbeBundle.Bnil : ProbeBundle ProbeName) h BHist.Empty := by
  exact SigRel.empty h

theorem sig_cons_constructor {pi : ProbeName} {tail : ProbeBundle ProbeName}
    {h s r : BHist} {m : BMark} {delta : Evidence} :
    Ask pi h m delta -> SigRel tail h s -> Ext s m r ->
      SigRel (ProbeBundle.Bcons pi tail) h r := by
  intro hask htail hext
  exact SigRel.cons pi tail h s r m delta hask htail hext

theorem sig_cons_inversion {pi : ProbeName} {tail : ProbeBundle ProbeName} {h r : BHist} :
    SigRel (ProbeBundle.Bcons pi tail) h r →
      ∃ s : BHist, ∃ m : BMark, ∃ delta : Evidence,
        Ask pi h m delta ∧ SigRel tail h s ∧ Ext s m r := by
  intro hsig
  cases hsig with
  | cons _ _ _ s _ m delta hask htail hext =>
      exact ⟨s, m, delta, hask, htail, hext⟩

omit [AskSetup] in
theorem sig_cons_head_mark_determinacy [AskSetup] {pi : ProbeName} {tail : ProbeBundle ProbeName}
    {D : BHist → Prop} {h r r' : BHist} (policy : AskPolicy D) :
    D h → SigRel (ProbeBundle.Bcons pi tail) h r →
      SigRel (ProbeBundle.Bcons pi tail) h r' →
      ∃ s : BHist, ∃ t : BHist, ∃ m : BMark, ∃ n : BMark,
      ∃ delta : Evidence, ∃ theta : Evidence,
        Ask pi h m delta ∧ Ask pi h n theta ∧
        SigRel tail h s ∧ SigRel tail h t ∧ msame m n := by
  intro _ left right
  cases left with
  | cons _ _ _ s _ m delta leftAsk leftTail _ =>
      cases right with
      | cons _ _ _ t _ n theta rightAsk rightTail _ =>
          exact Exists.intro s
            (Exists.intro t
              (Exists.intro m
                (Exists.intro n
                  (Exists.intro delta
                    (Exists.intro theta
                      (And.intro leftAsk
                        (And.intro rightAsk
                          (And.intro leftTail
                            (And.intro rightTail
                              (policy.deterministic leftAsk rightAsk))))))))))

theorem sig_cons_result_inversion [AskSetup] {pi : ProbeName} {tail : ProbeBundle ProbeName}
    {h r : BHist} :
    SigRel (ProbeBundle.Bcons pi tail) h r ->
      exists s : BHist, exists m : BMark, exists delta : Evidence,
        Ask pi h m delta /\ SigRel tail h s /\
          ((m = BMark.b0 /\ r = BHist.e0 s) \/ (m = BMark.b1 /\ r = BHist.e1 s)) := by
  intro hsig
  cases sig_cons_inversion hsig with
  | intro s rest =>
      cases rest with
      | intro m rest =>
          cases rest with
          | intro delta data =>
              cases data with
              | intro hask tailAndExt =>
                  cases tailAndExt with
                  | intro htail hext =>
                      exact Exists.intro s
                        (Exists.intro m
                          (Exists.intro delta
                            (And.intro hask
                              (And.intro htail (ext_constructor_inversion hext)))))

theorem sigRel_cons_inversion {pi : ProbeName} {tail : ProbeBundle ProbeName} {h r : BHist} :
    SigRel (ProbeBundle.Bcons pi tail) h r →
      ∃ s : BHist, ∃ m : BMark, ∃ delta : Evidence,
        Ask pi h m delta ∧ SigRel tail h s ∧ Ext s m r := by
  intro hsig
  exact sig_cons_inversion hsig

theorem sig_empty_inversion {h r : BHist} :
    SigRel (ProbeBundle.Bnil : ProbeBundle ProbeName) h r -> hsame r BHist.Empty := by
  intro hsig
  cases hsig
  rfl

def SameSig (bundle : ProbeBundle ProbeName) (h k : BHist) : Prop :=
  ∃ s : BHist, ∃ t : BHist, SigRel bundle h s ∧ SigRel bundle k t ∧ hsame s t

def SigTotalOn (bundle : ProbeBundle ProbeName) (D : BHist → Prop) : Prop :=
  ∀ h : BHist, D h → ∃ s : BHist, SigRel bundle h s

theorem sig_total_from_policy :
    ∀ {bundle : ProbeBundle ProbeName} {D : BHist → Prop} {h : BHist},
      AskPolicy D → D h → ∃ s : BHist, SigRel bundle h s := by
  intro bundle
  induction bundle with
  | Bnil =>
      intro D h policy hd
      exact ⟨BHist.Empty, SigRel.empty h⟩
  | Bcons pi tail ih =>
      intro D h policy hd
      cases policy.total (π := pi) (h := h) hd with
      | intro m hmark =>
          cases hmark with
          | intro delta hask =>
              cases ih (D := D) (h := h) policy hd with
              | intro s hsig =>
                  cases m with
                  | b0 =>
                      exact ⟨BHist.e0 s, SigRel.cons pi tail h s (BHist.e0 s) BMark.b0 delta hask hsig (Ext.e0 s)⟩
                  | b1 =>
                      exact ⟨BHist.e1 s, SigRel.cons pi tail h s (BHist.e1 s) BMark.b1 delta hask hsig (Ext.e1 s)⟩

omit [AskSetup] in
theorem sigTotalOn_from_policy [AskSetup] {bundle : ProbeBundle ProbeName} {D : BHist -> Prop} :
    AskPolicy D -> SigTotalOn bundle D := by
  intro policy
  intro h hd
  exact sig_total_from_policy (bundle := bundle) (D := D) (h := h) policy hd

theorem sig_deterministic :
    ∀ {bundle : ProbeBundle ProbeName} {D : BHist → Prop} {h s t : BHist},
      AskPolicy D → D h → SigRel bundle h s → SigRel bundle h t → hsame s t := by
  intro bundle D h s t pol hh hs ht
  induction bundle generalizing h s t with
  | Bnil =>
      cases hs
      cases ht
      rfl
  | Bcons pi tail ih =>
      cases hs with
      | cons _ _ _ s _ m _ ask hs' hx =>
          cases ht with
          | cons _ _ _ t _ m' _ ask' ht' hy =>
              have hsameTail : hsame s t := ih hh hs' ht'
              have hm : msame m m' := pol.deterministic ask ask'
              exact ext_respects_sameness hsameTail hm hx hy

omit [AskSetup] in
theorem sig_cons_tail_deterministic [AskSetup] {pi : ProbeName} {tail : ProbeBundle ProbeName}
    {D : BHist -> Prop} {h r r' : BHist} :
    AskPolicy D -> D h -> SigRel (ProbeBundle.Bcons pi tail) h r ->
      SigRel (ProbeBundle.Bcons pi tail) h r' ->
      exists s : BHist, exists t : BHist,
        SigRel tail h s /\ SigRel tail h t /\ hsame s t := by
  intro policy dh left right
  cases left with
  | cons _ _ _ s _ _ _ _ leftTail _ =>
      cases right with
      | cons _ _ _ t _ _ _ _ rightTail _ =>
          exact Exists.intro s
            (Exists.intro t
              (And.intro leftTail
                (And.intro rightTail
                  (sig_deterministic
                    (bundle := tail)
                    (D := D)
                    (h := h)
                    (s := s)
                    (t := t)
                    policy
                    dh
                    leftTail
                    rightTail))))

theorem sig_respects_history :
    ∀ {bundle : ProbeBundle ProbeName} {D : BHist → Prop} {h k s t : BHist},
      AskPolicy D → hsame h k → SigRel bundle h s → SigRel bundle k t → hsame s t := by
  intro bundle
  induction bundle with
  | Bnil =>
      intro D h k s t pol hhk hs ht
      cases hs
      cases ht
      rfl
  | Bcons pi tail ih =>
      intro D h k s t pol hhk hs ht
      cases hs with
      | cons _ _ _ s0 _ m delta ask hsTail hx =>
          cases ht with
          | cons _ _ _ t0 _ m' delta' ask' htTail hy =>
              have hsameTail : hsame s0 t0 := ih pol hhk hsTail htTail
              have hm : msame m m' := pol.respectsHistory hhk ask ask'
              exact ext_respects_sameness hsameTail hm hx hy

omit [AskSetup] in
theorem sameSig_of_hsame_under_policy [AskSetup] {bundle : ProbeBundle ProbeName}
    {D : BHist → Prop} {h k : BHist} (policy : AskPolicy D)
    (total : SigTotalOn bundle D) :
    D h → D k → hsame h k → SameSig bundle h k := by
  intro hIn kIn hhk
  cases total h hIn with
  | intro s hs =>
      cases total k kIn with
      | intro t ht =>
          exact ⟨s, t, hs, ht, sig_respects_history policy hhk hs ht⟩

theorem sameSig_of_hsame_from_ask_policy :
    forall {bundle : ProbeBundle ProbeName} {D : BHist -> Prop} {h k : BHist},
      AskPolicy D -> D h -> D k -> hsame h k -> SameSig bundle h k := by
  intro bundle D h k policy dh dk hhk
  have total : SigTotalOn bundle D := by
    intro h0 hIn
    exact sig_total_from_policy (bundle := bundle) (D := D) (h := h0) policy hIn
  exact sameSig_of_hsame_under_policy
    (bundle := bundle) (D := D) (h := h) (k := k)
    policy total dh dk hhk

theorem sameSig_refl :
    ∀ {bundle : ProbeBundle ProbeName} {D : BHist → Prop} {h : BHist},
      SigTotalOn bundle D → D h → SameSig bundle h h := by
  intro bundle D h htotal hh
  rcases htotal h hh with ⟨s, hs⟩
  exact ⟨s, s, hs, hs, hsame_refl s⟩

theorem sameSig_symm :
    ∀ {bundle : ProbeBundle ProbeName} {h k : BHist}, SameSig bundle h k → SameSig bundle k h := by
  intro bundle h k hs
  rcases hs with ⟨s, t, hs, ht, hst⟩
  exact ⟨t, s, ht, hs, hsame_symm hst⟩

theorem sameSig_trans_from_middle_determinacy {bundle : ProbeBundle ProbeName} {h k l : BHist}
    (middleDet : ∀ {s t : BHist}, SigRel bundle k s → SigRel bundle k t → hsame s t) :
    SameSig bundle h k → SameSig bundle k l → SameSig bundle h l := by
  intro hhk hkl
  cases hhk with
  | intro s hhkTail =>
      cases hhkTail with
      | intro t hhkData =>
          cases hhkData with
          | intro hs hhkRest =>
              cases hhkRest with
              | intro htk hst =>
                  cases hkl with
                  | intro u hklTail =>
                      cases hklTail with
                      | intro v hklData =>
                          cases hklData with
                          | intro huk hklRest =>
                              cases hklRest with
                              | intro hvl huv =>
                                  have htu : hsame t u := middleDet htk huk
                                  exact Exists.intro s
                                    (Exists.intro v
                                      (And.intro hs
                                        (And.intro hvl
                                          (hsame_trans hst (hsame_trans htu huv)))))

theorem sameSig_trans :
    ∀ {bundle : ProbeBundle ProbeName} {D : BHist → Prop} {h k l : BHist},
      AskPolicy D → D k → SameSig bundle h k → SameSig bundle k l → SameSig bundle h l := by
  intro bundle D h k l pol hk hhk hkl
  rcases hhk with ⟨s, t, hs, htk, hst⟩
  rcases hkl with ⟨u, v, huk, hvl, huv⟩
  have htu : hsame t u :=
    sig_deterministic (bundle := bundle) (D := D) (h := k) (s := t) (t := u) pol hk htk huk
  exact ⟨s, v, hs, hvl, hsame_trans hst (hsame_trans htu huv)⟩

theorem sameSig_trans_under_policy {bundle : ProbeBundle ProbeName} {D : BHist -> Prop}
    (policy : AskPolicy D) {h k l : BHist} :
    D k -> SameSig bundle h k -> SameSig bundle k l -> SameSig bundle h l := by
  intro hk hhk hkl
  cases hhk with
  | intro s hhkTail =>
      cases hhkTail with
      | intro t hhkData =>
          cases hhkData with
          | intro hs hhkRest =>
              cases hhkRest with
              | intro htk hst =>
                  cases hkl with
                  | intro u hklTail =>
                      cases hklTail with
                      | intro v hklData =>
                          cases hklData with
                          | intro huk hklRest =>
                              cases hklRest with
                              | intro hvl huv =>
                                  have htu : hsame t u :=
                                    sig_deterministic
                                      (bundle := bundle)
                                      (D := D)
                                      (h := k)
                                      (s := t)
                                      (t := u)
                                      policy
                                      hk
                                      htk
                                      huk
                                  exact Exists.intro s
                                    (Exists.intro v
                                      (And.intro hs
                                        (And.intro hvl
                                          (hsame_trans hst (hsame_trans htu huv)))))

theorem sameSig_equivalence {bundle : ProbeBundle ProbeName} {D : BHist → Prop} (policy : AskPolicy D) :
    (∀ {h : BHist}, D h → SameSig bundle h h) ∧
      (∀ {h k : BHist}, SameSig bundle h k → SameSig bundle k h) ∧
      (∀ {h k l : BHist}, D k → SameSig bundle h k → SameSig bundle k l → SameSig bundle h l) := by
  constructor
  · intro h hd
    cases sig_total_from_policy (bundle := bundle) (D := D) (h := h) policy hd with
    | intro s hsig =>
        exact ⟨s, s, hsig, hsig, hsame_refl s⟩
  · constructor
    · intro h k hsameSig
      cases hsameSig with
      | intro s hsameSigTail =>
          cases hsameSigTail with
          | intro t hsameSigData =>
              cases hsameSigData with
              | intro hs hsameSigRest =>
                  cases hsameSigRest with
                  | intro ht hst =>
                      exact ⟨t, s, ht, hs, hsame_symm hst⟩
    · intro h k l hk hhk hkl
      cases hhk with
      | intro s hhkTail =>
          cases hhkTail with
          | intro t hhkData =>
              cases hhkData with
              | intro hs hhkRest =>
                  cases hhkRest with
                  | intro htk hst =>
                      cases hkl with
                      | intro u hklTail =>
                          cases hklTail with
                          | intro v hklData =>
                              cases hklData with
                              | intro huk hklRest =>
                                  cases hklRest with
                                  | intro hvl huv =>
                                      have htu : hsame t u :=
                                        sig_deterministic
                                          (bundle := bundle)
                                          (D := D)
                                          (h := k)
                                          (s := t)
                                          (t := u)
                                          policy
                                          hk
                                          htk
                                          huk
                                      exact ⟨s, v, hs, hvl, hsame_trans hst (hsame_trans htu huv)⟩

omit [AskSetup] in
theorem sameSig_equivalence_under_policy [AskSetup] {bundle : ProbeBundle ProbeName} {D : BHist → Prop}
    (policy : AskPolicy D) :
    (∀ {h : BHist}, D h → SameSig bundle h h) ∧
      (∀ {h k : BHist}, SameSig bundle h k → SameSig bundle k h) ∧
      (∀ {h k l : BHist}, D k → SameSig bundle h k → SameSig bundle k l → SameSig bundle h l) := by
  exact sameSig_equivalence (bundle := bundle) (D := D) policy

end BEDC.FKernel.Sig
