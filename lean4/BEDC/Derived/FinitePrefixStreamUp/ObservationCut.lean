import BEDC.Derived.FinitePrefixStreamUp.NameCertObligations

namespace BEDC.Derived.FinitePrefixStreamUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Unary

def FinitePrefixStreamCertificateObservationCut
    (source window prefixRow proofRow : BHist) : Prop :=
  -- BEDC touchpoint anchor: BHist Cont hsame UnaryHistory
  UnaryHistory source ∧ UnaryHistory window ∧ UnaryHistory prefixRow ∧
    Cont source window prefixRow ∧ hsame proofRow prefixRow

theorem FinitePrefixStreamCertificateObservationCut_visible_boundary
    {source window prefixRow proofRow : BHist} :
    FinitePrefixStreamCertificateObservationCut source window prefixRow proofRow →
      UnaryHistory prefixRow ∧ Cont source window prefixRow ∧ hsame proofRow prefixRow := by
  -- BEDC touchpoint anchor: BHist Cont hsame UnaryHistory
  intro cut
  exact ⟨cut.right.right.left, cut.right.right.right.left, cut.right.right.right.right⟩

end BEDC.Derived.FinitePrefixStreamUp
