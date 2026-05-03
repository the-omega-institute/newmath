import BEDC.Derived.AdjunctionUp
import BEDC.Derived.CategoryUp.Cycle
import BEDC.FKernel.NameCert

namespace BEDC.Derived.EquivCatUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Cont
open BEDC.FKernel.NameCert
open BEDC.Derived.AdjunctionUp
open BEDC.Derived.CategoryUp
open BEDC.Derived.NatTransUp

theorem EquivCatAdjunction_empty_roundtrip_identity_components
    {p q a unit counit left right : BHist} :
    AdjunctionUnitCounitCarrier p q a unit counit left right ->
      hsame left BHist.Empty -> hsame right BHist.Empty ->
        NatTransPrefixComponentCarrier p q a BHist.Empty ∧
          NatTransPrefixComponentCarrier q p a BHist.Empty := by
  intro carrier leftEmpty rightEmpty
  have unitCounitEmpty : unit = BHist.Empty ∧ counit = BHist.Empty := by
    cases leftEmpty
    exact cont_empty_result_inversion carrier.right.right.left
  have counitUnitEmpty : counit = BHist.Empty ∧ unit = BHist.Empty := by
    cases rightEmpty
    exact cont_empty_result_inversion carrier.right.right.right
  cases unitCounitEmpty.left
  cases unitCounitEmpty.right
  cases counitUnitEmpty.left
  cases counitUnitEmpty.right
  exact And.intro carrier.left carrier.right.left

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
