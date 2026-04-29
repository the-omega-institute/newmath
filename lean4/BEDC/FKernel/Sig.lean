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

def SameSig (bundle : ProbeBundle ProbeName) (h k : BHist) : Prop :=
  ∃ s : BHist, ∃ t : BHist, SigRel bundle h s ∧ SigRel bundle k t ∧ hsame s t

def SigTotalOn (bundle : ProbeBundle ProbeName) (D : BHist → Prop) : Prop :=
  ∀ h : BHist, D h → ∃ s : BHist, SigRel bundle h s

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

theorem sameSig_trans :
    ∀ {bundle : ProbeBundle ProbeName} {D : BHist → Prop} {h k l : BHist},
      AskPolicy D → D k → SameSig bundle h k → SameSig bundle k l → SameSig bundle h l := by
  intro bundle D h k l pol hk hhk hkl
  rcases hhk with ⟨s, t, hs, htk, hst⟩
  rcases hkl with ⟨u, v, huk, hvl, huv⟩
  have htu : hsame t u :=
    sig_deterministic (bundle := bundle) (D := D) (h := k) (s := t) (t := u) pol hk htk huk
  exact ⟨s, v, hs, hvl, hsame_trans hst (hsame_trans htu huv)⟩

end BEDC.FKernel.Sig
