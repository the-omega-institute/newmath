import BEDC.Derived.CategoryUp.Cycle
import BEDC.FKernel.NameCert

namespace BEDC.Derived.EquivCatUp

open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.Derived.CategoryUp

theorem EquivCatCycleIdentityCarrier_semanticNameCert {a b f g : BHist}
    (left : CategoryHomCarrier a b f) (right : CategoryHomCarrier b a g) :
    SemanticNameCert
      (fun t : BHist =>
        CategoryHomCarrier a b t ∧ CategoryHomCarrier b a g ∧ hsame t BHist.Empty ∧
          hsame g BHist.Empty)
      (fun t : BHist =>
        CategoryHomCarrier a b t ∧ CategoryHomCarrier b a g ∧ hsame t BHist.Empty ∧
          hsame g BHist.Empty)
      (fun t : BHist =>
        CategoryHomCarrier a b t ∧ CategoryHomCarrier b a g ∧ hsame t BHist.Empty ∧
          hsame g BHist.Empty)
      hsame := by
  have cycle := CategoryHomCarrier_cycle_tails_empty left right
  constructor
  · constructor
    · exact Exists.intro BHist.Empty
        (And.intro
          (CategoryHomCarrier_hsame_transport (hsame_refl a) (hsame_refl b)
            cycle.right.left left)
          (And.intro right (And.intro (hsame_refl BHist.Empty) cycle.right.right)))
    · intro h _carrier
      exact hsame_refl h
    · intro h k same
      exact hsame_symm same
    · intro h k r sameHK sameKR
      exact hsame_trans sameHK sameKR
    · intro h k same carrier
      exact And.intro
        (CategoryHomCarrier_hsame_transport (hsame_refl a) (hsame_refl b) same carrier.left)
        (And.intro carrier.right.left
          (And.intro (hsame_trans (hsame_symm same) carrier.right.right.left)
            carrier.right.right.right))
  · intro h source
    exact source
  · intro h source
    exact source

end BEDC.Derived.EquivCatUp
