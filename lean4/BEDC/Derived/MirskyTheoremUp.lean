import BEDC.FKernel.Hist

namespace BEDC.Derived

open BEDC.FKernel.Hist

inductive MirskyTheoremUp : Type where
  | mk (O H A R K S T C P N : BHist) : MirskyTheoremUp

end BEDC.Derived
