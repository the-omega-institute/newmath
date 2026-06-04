import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.LowerSemicontinuousUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def LowerSemicontinuousSuperlevelThresholdSurface [AskSetup] [PackageSetup]
    (threshold epigraph located boundary transport replay provenance localName : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  -- BEDC touchpoint anchor: BHist Cont hsame ProbeBundle PkgSig UnaryHistory
  UnaryHistory threshold ∧
    UnaryHistory epigraph ∧
      UnaryHistory located ∧
        UnaryHistory boundary ∧
          UnaryHistory transport ∧
            UnaryHistory replay ∧
              UnaryHistory provenance ∧
                UnaryHistory localName ∧
                  Cont epigraph located boundary ∧
                    Cont boundary transport replay ∧
                      hsame transport localName ∧ PkgSig bundle provenance pkg

theorem LowerSemicontinuousSuperlevelThresholdSurface_threshold_route [AskSetup]
    [PackageSetup]
    {threshold epigraph located boundary transport replay provenance localName : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    LowerSemicontinuousSuperlevelThresholdSurface threshold epigraph located boundary
        transport replay provenance localName bundle pkg →
      UnaryHistory threshold ∧ Cont epigraph located boundary ∧
        PkgSig bundle provenance pkg := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle PkgSig UnaryHistory
  intro surface
  exact ⟨surface.left, surface.right.right.right.right.right.right.right.right.left,
    surface.right.right.right.right.right.right.right.right.right.right.right⟩

end BEDC.Derived.LowerSemicontinuousUp
