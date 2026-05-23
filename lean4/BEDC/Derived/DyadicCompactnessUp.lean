import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def DyadicCompactnessUp [AskSetup] [PackageSetup]
    (interval rationalCells dyadicCells mesh centers coverage streamWindows regularReadback realSeal
      transport replay provenance nameRow : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  UnaryHistory interval ∧ UnaryHistory rationalCells ∧ UnaryHistory dyadicCells ∧
    UnaryHistory mesh ∧ UnaryHistory centers ∧ UnaryHistory coverage ∧
      UnaryHistory streamWindows ∧ UnaryHistory regularReadback ∧ UnaryHistory realSeal ∧
        UnaryHistory transport ∧ UnaryHistory replay ∧ UnaryHistory provenance ∧
          UnaryHistory nameRow ∧ Cont interval rationalCells dyadicCells ∧
            Cont dyadicCells mesh centers ∧ Cont centers coverage streamWindows ∧
              Cont streamWindows regularReadback realSeal ∧ Cont realSeal transport replay ∧
                Cont replay provenance nameRow ∧ PkgSig bundle nameRow pkg

end BEDC.Derived
