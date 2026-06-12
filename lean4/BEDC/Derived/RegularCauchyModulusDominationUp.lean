import BEDC.FKernel.Hist

namespace BEDC.Derived

open BEDC.FKernel.Hist

inductive RegularCauchyModulusDominationUp : Type where
  | mk
      (sourceModulus dominatingModulus dominationLedger sourceWindow dominatingWindow
        cofinalTail regularReadback realSeal transport replay provenance name : BHist) :
      RegularCauchyModulusDominationUp

end BEDC.Derived
