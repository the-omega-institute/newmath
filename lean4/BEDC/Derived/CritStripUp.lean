import BEDC.Derived.NatUp

namespace BEDC.Derived.CritStripUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Cont
open BEDC.FKernel.Unary
open BEDC.Derived.NatUp

def CritStripOpenInterval (sigma : BHist) : Prop :=
  NatUnaryStrictPrefix BHist.Empty sigma ∧
    NatUnaryStrictPrefix sigma (BHist.e1 BHist.Empty)

theorem CritStripOpenInterval_unary_boundary_exclusion {sigma : BHist} :
    CritStripOpenInterval sigma ->
      UnaryHistory sigma ∧ (hsame sigma BHist.Empty -> False) ∧
        (hsame sigma (BHist.e1 BHist.Empty) -> False) := by
  intro strip
  have sigmaUnary : UnaryHistory sigma := by
    cases strip.left with
    | intro tail data =>
        have sameSigmaTail : hsame sigma tail := cont_left_unit_result data.right.right
        exact unary_transport data.left (hsame_symm sameSigmaTail)
  constructor
  · exact sigmaUnary
  · constructor
    · intro sameEmpty
      cases sameEmpty
      exact NatUnaryStrictPrefix_empty_right_absurd strip.left
    · intro sameOne
      cases sameOne
      exact NatUnaryStrictPrefix_asymm strip.right strip.right

def InCritStrip (sigma : BHist) : Prop :=
  NatUnaryStrictPrefix BHist.Empty sigma ∧
    NatUnaryStrictPrefix sigma (BHist.e1 BHist.Empty)

theorem InCritStrip_boundary_excluded {sigma : BHist} :
    InCritStrip sigma ->
      (hsame sigma BHist.Empty -> False) ∧
        (hsame sigma (BHist.e1 BHist.Empty) -> False) := by
  intro strip
  constructor
  · intro sameEmpty
    cases sameEmpty
    exact NatUnaryStrictPrefix_asymm strip.left strip.left
  · intro sameUnit
    cases sameUnit
    exact NatUnaryStrictPrefix_asymm strip.right strip.right

end BEDC.Derived.CritStripUp
