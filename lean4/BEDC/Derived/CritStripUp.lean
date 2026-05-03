import BEDC.Derived.NatUp
import BEDC.Derived.RatUp

namespace BEDC.Derived.CritStripUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Cont
open BEDC.FKernel.Unary
open BEDC.Derived.NatUp
open BEDC.Derived.RatUp

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

theorem InCritStrip_hsame_transport_boundary_exclusion {sigma sigma' : BHist} :
    InCritStrip sigma -> hsame sigma sigma' ->
      InCritStrip sigma' ∧ (hsame sigma' BHist.Empty -> False) ∧
        (hsame sigma' (BHist.e1 BHist.Empty) -> False) := by
  intro strip sameSigma
  have leftStrict : NatUnaryStrictPrefix BHist.Empty sigma' := by
    cases strip.left with
    | intro tail data =>
        exact NatUnaryStrictPrefix_cont_hsame_transport data.left data.right.left
          data.right.right (hsame_refl BHist.Empty) sameSigma
  have rightStrict : NatUnaryStrictPrefix sigma' (BHist.e1 BHist.Empty) := by
    cases strip.right with
    | intro tail data =>
        exact NatUnaryStrictPrefix_cont_hsame_transport data.left data.right.left
          data.right.right sameSigma (hsame_refl (BHist.e1 BHist.Empty))
  have transported : InCritStrip sigma' := And.intro leftStrict rightStrict
  exact And.intro transported (InCritStrip_boundary_excluded transported)

def CritStripComplexCarrier (s sigma tau : BHist) : Prop :=
  RatHistoryCarrier sigma ∧ RatHistoryCarrier tau ∧ Cont sigma tau s ∧ InCritStrip sigma

theorem CritStripComplexCarrier_not_empty {s sigma tau : BHist} :
    CritStripComplexCarrier s sigma tau -> hsame s BHist.Empty -> False := by
  intro carrier sameEmpty
  have emptyCont : Cont sigma tau BHist.Empty :=
    cont_result_hsame_transport carrier.right.right.left sameEmpty
  have endpoints : sigma = BHist.Empty ∧ tau = BHist.Empty :=
    cont_empty_result_inversion emptyCont
  exact RatHistoryCarrier_not_empty carrier.left endpoints.left

end BEDC.Derived.CritStripUp
