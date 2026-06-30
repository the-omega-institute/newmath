import BEDC.Derived.ResultantUp

namespace BEDC.Derived

structure PolynomialResultantUp where
  degreeF : Nat
  degreeG : Nat
  polynomialRows : BEDC.Derived.ResultantUp.Poly × BEDC.Derived.ResultantUp.Poly
  sylvesterMatrixRow : BEDC.Derived.ResultantUp.Matrix
  fieldDeterminantRow : BEDC.Derived.ResultantUp.Z

end BEDC.Derived
