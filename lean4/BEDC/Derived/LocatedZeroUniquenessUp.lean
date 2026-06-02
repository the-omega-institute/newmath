import BEDC.FKernel.Hist

namespace BEDC.Derived

open BEDC.FKernel.Hist

inductive LocatedZeroUniquenessUp : Type where
  | mk
      (bracket modulus schedule zeroLeft zeroRight streamLeft streamRight readLeft readRight
        tolerance comparison transport replay provenance localName : BHist) :
      LocatedZeroUniquenessUp
  deriving DecidableEq

end BEDC.Derived
