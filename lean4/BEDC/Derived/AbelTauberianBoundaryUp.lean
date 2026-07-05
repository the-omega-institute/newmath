import BEDC.FKernel.Hist

open BEDC.FKernel.Hist

namespace BEDC
namespace Derived

inductive AbelTauberianBoundaryUp : Type where
  | mk (S L T R E H C P N : BHist) : AbelTauberianBoundaryUp
  deriving DecidableEq

end Derived
end BEDC
