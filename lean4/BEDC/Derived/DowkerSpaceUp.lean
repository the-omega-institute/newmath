import BEDC.FKernel.Hist

namespace BEDC.Derived

open BEDC.FKernel.Hist

inductive DowkerSpaceUp : Type where
  | mk
      (topology normalSource obstruction paracompactComparison intervalProductTest transport
        replay provenance localNameCert : BHist) :
      DowkerSpaceUp
  deriving DecidableEq

end BEDC.Derived
