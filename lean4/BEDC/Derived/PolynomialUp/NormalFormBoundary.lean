import BEDC.Derived.PolynomialUp

namespace BEDC.Derived.PolynomialUp

open BEDC.FKernel.Hist

def PolynomialSingletonNormalizedRepresentative (c : BHist) : Prop :=
  PolynomialSingletonCarrier c ∧ (hsame c BHist.Empty -> False)

end BEDC.Derived.PolynomialUp
