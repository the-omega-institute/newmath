import BEDC.FKernel.Sig

namespace BEDC.FKernel.Sig

open BEDC.FKernel.Mark
open BEDC.FKernel.Hist
open BEDC.FKernel.Ext
open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle

theorem signature_determinacy_proof_spine [AskSetup] {bundle : ProbeBundle ProbeName}
    {D : BHist -> Prop} {h s t : BHist} :
    AskPolicy D → D h → SigRel bundle h s → SigRel bundle h t → hsame s t := by
  intro policy dh left right
  induction bundle generalizing h s t with
  | Bnil =>
      cases left
      cases right
      rfl
  | Bcons pi tail ih =>
      cases left with
      | cons _ _ _ sTail _ m _ leftAsk leftTail leftExt =>
          cases right with
          | cons _ _ _ tTail _ n _ rightAsk rightTail rightExt =>
              have tailSame : hsame sTail tTail :=
                ih
                  (h := h)
                  (s := sTail)
                  (t := tTail)
                  dh
                  leftTail
                  rightTail
              have markSame : msame m n := policy.deterministic leftAsk rightAsk
              exact ext_respects_sameness tailSame markSame leftExt rightExt

theorem signature_determinacy_spine [AskSetup] {bundle : ProbeBundle ProbeName}
    {D : BHist -> Prop} {h s t : BHist} :
    AskPolicy D -> D h -> SigRel bundle h s -> SigRel bundle h t -> hsame s t := by
  intro policy dh left right
  induction bundle generalizing h s t with
  | Bnil =>
      cases left
      cases right
      rfl
  | Bcons pi tail ih =>
      cases left with
      | cons _ _ _ sTail _ m _ leftAsk leftTail leftExt =>
          cases right with
          | cons _ _ _ tTail _ n _ rightAsk rightTail rightExt =>
              have tailSame : hsame sTail tTail :=
                ih
                  (h := h)
                  (s := sTail)
                  (t := tTail)
                  dh
                  leftTail
                  rightTail
              have markSame : msame m n := policy.deterministic leftAsk rightAsk
              exact ext_respects_sameness tailSame markSame leftExt rightExt

theorem sig_cons_result_hsame_from_policy [AskSetup]
    {pi : ProbeName} {tail : ProbeBundle ProbeName}
    {D : BHist -> Prop} {h r r' : BHist} (policy : AskPolicy D) :
    D h -> SigRel (ProbeBundle.Bcons pi tail) h r ->
      SigRel (ProbeBundle.Bcons pi tail) h r' -> hsame r r' := by
  intro dh left right
  cases left with
  | cons _ _ _ s _ m _ leftAsk leftTail leftExt =>
      cases right with
      | cons _ _ _ t _ n _ rightAsk rightTail rightExt =>
          have tailSame : hsame s t :=
            sig_deterministic
              (bundle := tail)
              (D := D)
              (h := h)
              (s := s)
              (t := t)
              policy
              dh
              leftTail
              rightTail
          have markSame : msame m n := policy.deterministic leftAsk rightAsk
          exact ext_respects_sameness tailSame markSame leftExt rightExt

theorem sig_cons_tail_hsame_from_policy [AskSetup]
    {pi : ProbeName} {tail : ProbeBundle ProbeName}
    {D : BHist → Prop} {h r r' : BHist} (policy : AskPolicy D) :
    D h → SigRel (ProbeBundle.Bcons pi tail) h r →
      SigRel (ProbeBundle.Bcons pi tail) h r' →
      ∃ s : BHist, ∃ t : BHist, SigRel tail h s ∧ SigRel tail h t ∧ hsame s t := by
  intro dh left right
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

theorem sig_cons_policy_result_and_tail [AskSetup]
    {pi : ProbeName} {tail : ProbeBundle ProbeName}
    {D : BHist → Prop} {h r r' : BHist} (policy : AskPolicy D) :
    D h → SigRel (ProbeBundle.Bcons pi tail) h r →
      SigRel (ProbeBundle.Bcons pi tail) h r' →
      (∃ s : BHist, ∃ t : BHist, SigRel tail h s ∧ SigRel tail h t ∧ hsame s t) ∧
        hsame r r' := by
  intro dh left right
  exact And.intro
    (sig_cons_tail_hsame_from_policy
      (pi := pi)
      (tail := tail)
      (D := D)
      (h := h)
      (r := r)
      (r' := r')
      policy
      dh
      left
      right)
    (sig_cons_result_hsame_from_policy
      (pi := pi)
      (tail := tail)
      (D := D)
      (h := h)
      (r := r)
      (r' := r')
      policy
      dh
      left
      right)

theorem sig_cons_head_tail_determinacy [AskSetup]
    {pi : ProbeName} {tail : ProbeBundle ProbeName}
    {D : BHist → Prop} {h r r' : BHist} (policy : AskPolicy D) :
    D h → SigRel (ProbeBundle.Bcons pi tail) h r →
      SigRel (ProbeBundle.Bcons pi tail) h r' →
      ∃ s : BHist, ∃ t : BHist, ∃ m : BMark, ∃ n : BMark,
      ∃ delta : Evidence, ∃ theta : Evidence,
        Ask pi h m delta ∧ Ask pi h n theta ∧
        SigRel tail h s ∧ SigRel tail h t ∧ msame m n ∧ hsame s t := by
  intro dh left right
  cases left with
  | cons _ _ _ s _ m delta leftAsk leftTail _ =>
      cases right with
      | cons _ _ _ t _ n theta rightAsk rightTail _ =>
          have markSame : msame m n := policy.deterministic leftAsk rightAsk
          have tailSame : hsame s t :=
            sig_deterministic
              (bundle := tail)
              (D := D)
              (h := h)
              (s := s)
              (t := t)
              policy
              dh
              leftTail
              rightTail
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
                              (And.intro markSame tailSame))))))))))

theorem signature_cons_head_mark_determinacy [AskSetup]
    {pi : ProbeName} {tail : ProbeBundle ProbeName}
    {D : BHist -> Prop} {h r r' : BHist} (policy : AskPolicy D) :
    D h -> SigRel (ProbeBundle.Bcons pi tail) h r ->
      SigRel (ProbeBundle.Bcons pi tail) h r' ->
      exists s : BHist, exists t : BHist, exists m : BMark, exists n : BMark,
      exists delta : Evidence, exists theta : Evidence,
        Ask pi h m delta /\ Ask pi h n theta /\
        SigRel tail h s /\ SigRel tail h t /\ msame m n := by
  intro _ left right
  cases left with
  | cons _ _ _ s _ m delta leftAsk leftTail _ =>
      cases right with
      | cons _ _ _ t _ n theta rightAsk rightTail _ =>
          have markSame : msame m n := policy.deterministic leftAsk rightAsk
          exact ⟨s, t, m, n, delta, theta, leftAsk, rightAsk, leftTail, rightTail, markSame⟩

theorem sig_cons_witnesses_and_result_hsame_from_policy [AskSetup]
    {pi : ProbeName} {tail : ProbeBundle ProbeName}
    {D : BHist → Prop} {h r r' : BHist} (policy : AskPolicy D) :
    D h → SigRel (ProbeBundle.Bcons pi tail) h r →
      SigRel (ProbeBundle.Bcons pi tail) h r' →
      ∃ s : BHist, ∃ t : BHist, ∃ m : BMark, ∃ n : BMark,
      ∃ delta : Evidence, ∃ theta : Evidence,
        Ask pi h m delta ∧ Ask pi h n theta ∧
        SigRel tail h s ∧ SigRel tail h t ∧
        msame m n ∧ hsame s t ∧ hsame r r' := by
  intro dh left right
  cases left with
  | cons _ _ _ s _ m delta leftAsk leftTail leftExt =>
      cases right with
      | cons _ _ _ t _ n theta rightAsk rightTail rightExt =>
          have markSame : msame m n := policy.deterministic leftAsk rightAsk
          have tailSame : hsame s t :=
            sig_deterministic
              (bundle := tail)
              (D := D)
              (h := h)
              (s := s)
              (t := t)
              policy
              dh
              leftTail
              rightTail
          have resultSame : hsame r r' :=
            ext_respects_sameness tailSame markSame leftExt rightExt
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
                              (And.intro markSame
                                (And.intro tailSame resultSame)))))))))))

end BEDC.FKernel.Sig
