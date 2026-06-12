import BEDC.FKernel.Hist

namespace BEDC.Derived

open BEDC.FKernel.Hist

inductive DyadicCompletionEmbeddingUp : Type where
  | carrier
      (source streamWindow regularReadback realSeal criterion transport replay provenance
        namecert : BHist) :
      DyadicCompletionEmbeddingUp

end BEDC.Derived
