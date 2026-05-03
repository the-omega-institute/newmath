import BEDC.Derived.NatUp

namespace BEDC.Derived.CritStripUp

open BEDC.FKernel.Hist
open BEDC.Derived.NatUp

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
