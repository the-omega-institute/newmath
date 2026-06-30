import BEDC.FKernel.Hist

namespace BEDC.Derived

open BEDC.FKernel.Hist

inductive HamiltonJacobiActionUp : Type where
  | mk
      (state timeWindow path velocity lagrangian action gradient hamiltonJacobi
        hamiltonJacobiBellman dynSystem ode matrix transport replay provenance localName : BHist) :
      HamiltonJacobiActionUp

end BEDC.Derived
