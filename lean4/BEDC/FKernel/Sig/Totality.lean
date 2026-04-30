import BEDC.FKernel.Sig

namespace BEDC.FKernel.Sig

open BEDC.FKernel.Mark
open BEDC.FKernel.Hist
open BEDC.FKernel.Ext
open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle

theorem signature_totality_under_policy [AskSetup] :
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
                      exact ⟨BHist.e0 s,
                        SigRel.cons pi tail h s (BHist.e0 s) BMark.b0 delta hask hsig
                          (Ext.e0 s)⟩
                  | b1 =>
                      exact ⟨BHist.e1 s,
                        SigRel.cons pi tail h s (BHist.e1 s) BMark.b1 delta hask hsig
                          (Ext.e1 s)⟩

theorem sig_total_unique_from_policy [AskSetup] {bundle : ProbeBundle ProbeName}
    {D : BHist → Prop} (policy : AskPolicy D) {h : BHist} :
    D h →
      ∃ s : BHist, SigRel bundle h s ∧
        ∀ {t : BHist}, SigRel bundle h t → hsame t s := by
  intro hd
  cases sig_total_from_policy (bundle := bundle) (D := D) (h := h) policy hd with
  | intro s hsig =>
      exact ⟨s, hsig, fun {t} ht => sig_deterministic policy hd ht hsig⟩

theorem sig_total_unique_pair_from_policy [AskSetup] {bundle : ProbeBundle ProbeName}
    {D : BHist -> Prop} (policy : AskPolicy D) {h : BHist} :
    D h ->
      exists s : BHist, SigRel bundle h s /\
        forall {t : BHist}, SigRel bundle h t -> hsame s t := by
  intro hd
  cases sig_total_unique_from_policy (bundle := bundle) (D := D) policy hd with
  | intro s data =>
      cases data with
      | intro hsig unique =>
          exact ⟨s, hsig, fun {t} ht => hsame_symm (unique ht)⟩

theorem sigTotalOn_cons_iff [AskSetup] {pi : ProbeName} {tail : ProbeBundle ProbeName}
    {D : BHist -> Prop} :
    SigTotalOn (ProbeBundle.Bcons pi tail) D <->
      (forall h : BHist, D h -> exists m : BMark, exists delta : Evidence,
        Ask pi h m delta) /\ SigTotalOn tail D := by
  constructor
  · intro total
    constructor
    · intro h hd
      cases total h hd with
      | intro r hsig =>
          cases hsig with
          | cons _ _ _ _ _ m delta hask _ _ =>
              exact Exists.intro m (Exists.intro delta hask)
    · intro h hd
      cases total h hd with
      | intro r hsig =>
          cases hsig with
          | cons _ _ _ s _ _ _ _ htail _ =>
              exact Exists.intro s htail
  · intro data
    cases data with
    | intro headTotal tailTotal =>
        intro h hd
        cases headTotal h hd with
        | intro m markData =>
            cases markData with
            | intro delta hask =>
                cases tailTotal h hd with
                | intro s htail =>
                    cases m with
                    | b0 =>
                        exact Exists.intro (BHist.e0 s)
                          (SigRel.cons pi tail h s (BHist.e0 s) BMark.b0 delta hask htail
                            (Ext.e0 s))
                    | b1 =>
                        exact Exists.intro (BHist.e1 s)
                          (SigRel.cons pi tail h s (BHist.e1 s) BMark.b1 delta hask htail
                            (Ext.e1 s))

end BEDC.FKernel.Sig
