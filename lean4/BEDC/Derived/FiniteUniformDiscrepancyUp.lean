import BEDC.FKernel.Cont
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived

open BEDC.FKernel.Hist

inductive FiniteUniformDiscrepancyUp : Type where
  | mk (L W Q E R S H C P N : BHist) : FiniteUniformDiscrepancyUp
  deriving DecidableEq

end BEDC.Derived

namespace BEDC.Derived.FiniteUniformDiscrepancyUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def FiniteUniformDiscrepancyCarrier [AskSetup] [PackageSetup]
    (L W Q E R S H C P N : BHist) (bundle : ProbeBundle ProbeName) (pkg : Pkg) :
    Prop :=
  UnaryHistory L ∧
    UnaryHistory W ∧
      UnaryHistory Q ∧
        UnaryHistory E ∧
          UnaryHistory R ∧
            UnaryHistory S ∧
              UnaryHistory H ∧
                UnaryHistory C ∧
                  UnaryHistory P ∧
                    UnaryHistory N ∧
                      hsame H H ∧
                        Cont L W C ∧ Cont Q E R ∧ Cont S R N ∧ PkgSig bundle P pkg

theorem FiniteUniformDiscrepancyCarrier_namecert_obligations [AskSetup] [PackageSetup]
    {L W Q E R S H C P N : BHist} {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    FiniteUniformDiscrepancyCarrier L W Q E R S H C P N bundle pkg →
      UnaryHistory L ∧
        UnaryHistory W ∧
          UnaryHistory Q ∧
            UnaryHistory E ∧
              UnaryHistory R ∧
                UnaryHistory S ∧
                  UnaryHistory H ∧
                    UnaryHistory C ∧
                      UnaryHistory P ∧
                        UnaryHistory N ∧
                          hsame H H ∧
                            Cont L W C ∧
                              Cont Q E R ∧ Cont S R N ∧ PkgSig bundle P pkg := by
  intro carrier
  exact carrier

end BEDC.Derived.FiniteUniformDiscrepancyUp
