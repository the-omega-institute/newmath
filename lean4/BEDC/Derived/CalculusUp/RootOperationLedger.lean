import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Hist
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.CalculusUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def CalculusRootOperationLedger [AskSetup] [PackageSetup]
    (C D I L R Q Y H T P N : BHist) (bundle : ProbeBundle ProbeName) (pkg : Pkg) :
    Prop :=
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg PkgSig hsame SemanticNameCert UnaryHistory
  UnaryHistory C ∧ UnaryHistory D ∧ UnaryHistory I ∧ UnaryHistory L ∧
    UnaryHistory R ∧ UnaryHistory Q ∧ UnaryHistory Y ∧ UnaryHistory H ∧
      UnaryHistory T ∧ PkgSig bundle P pkg ∧ PkgSig bundle N pkg ∧
        SemanticNameCert
          (fun row : BHist => hsame row R ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row C ∨ hsame row D ∨ hsame row I ∨ hsame row L ∨
              hsame row R ∨ hsame row Q ∨ hsame row Y ∨ hsame row H ∨
                hsame row T ∨ hsame row P ∨ hsame row N)
          (fun row : BHist =>
            UnaryHistory row ∧ PkgSig bundle P pkg ∧ PkgSig bundle N pkg)
          hsame

end BEDC.Derived.CalculusUp
