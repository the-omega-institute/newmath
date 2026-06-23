import BEDC.BaseReflection

namespace BEDC.Derived

open BEDC

inductive ClarksonInequalityUp : Type where
  | mk (lp norm exponent midpoint modulus real transport replay provenance name : BHist) :
      ClarksonInequalityUp

end BEDC.Derived
