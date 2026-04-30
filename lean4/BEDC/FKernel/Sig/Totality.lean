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

end BEDC.FKernel.Sig
