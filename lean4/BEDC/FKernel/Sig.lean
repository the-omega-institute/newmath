import BEDC.FKernel.Ext
import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle

/-! Signature generation compresses asking events into internal answer histories. -/
namespace BEDC.FKernel.Sig

open BEDC.FKernel.Mark
open BEDC.FKernel.Hist
open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle

axiom SigRel : ProbeBundle → BHist → BHist → Prop

def SameSig (bundle : ProbeBundle) (h k : BHist) : Prop :=
  ∃ s : BHist, ∃ t : BHist, SigRel bundle h s ∧ SigRel bundle k t ∧ hsame s t

def SigTotalOn (bundle : ProbeBundle) (D : BHist → Prop) : Prop :=
  ∀ h : BHist, D h → ∃ s : BHist, SigRel bundle h s

theorem sig_deterministic :
    ∀ {bundle : ProbeBundle} {D : BHist → Prop} {h s t : BHist},
      AskPolicy D → D h → SigRel bundle h s → SigRel bundle h t → hsame s t := by
  sorry

theorem sameSig_refl :
    ∀ {bundle : ProbeBundle} {D : BHist → Prop} {h : BHist},
      SigTotalOn bundle D → D h → SameSig bundle h h := by
  sorry

theorem sameSig_symm :
    ∀ {bundle : ProbeBundle} {h k : BHist}, SameSig bundle h k → SameSig bundle k h := by
  sorry

theorem sameSig_trans :
    ∀ {bundle : ProbeBundle} {h k l : BHist},
      SameSig bundle h k → SameSig bundle k l → SameSig bundle h l := by
  sorry

end BEDC.FKernel.Sig
