import BEDC.FKernel.Hist

namespace BEDC.Derived

open BEDC.FKernel.Hist

inductive AdamsBashforthFiniteStepUp : Type where
  | mk (O B W F S L H C P N : BHist) : AdamsBashforthFiniteStepUp

end BEDC.Derived
