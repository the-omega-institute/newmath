import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

/-!
# SliceCategoryUp finite carrier surface.
-/

namespace BEDC.Derived.SliceCategoryUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def SliceCategoryCarrier [AskSetup] [PackageSetup]
    (base displayed arrow fiber transport route provenance localName : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  -- BEDC touchpoint anchor: BHist UnaryHistory Cont ProbeBundle Pkg PkgSig hsame
  UnaryHistory base ∧ UnaryHistory displayed ∧ UnaryHistory arrow ∧ UnaryHistory fiber ∧
    UnaryHistory transport ∧ UnaryHistory route ∧ UnaryHistory provenance ∧
      UnaryHistory localName ∧ Cont displayed arrow base ∧ Cont route provenance localName ∧
        PkgSig bundle localName pkg ∧ hsame transport arrow

theorem SliceCategoryCarrier_kernel_fiber_obligation [AskSetup] [PackageSetup]
    {base displayed arrow fiber transport route provenance localName : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    SliceCategoryCarrier base displayed arrow fiber transport route provenance localName bundle pkg ->
      PkgSig bundle base pkg ->
        UnaryHistory base ∧ UnaryHistory displayed ∧ UnaryHistory arrow ∧
          Cont displayed arrow base ∧ Cont route provenance localName ∧ hsame transport arrow ∧
            PkgSig bundle localName pkg ∧ PkgSig bundle base pkg := by
  -- BEDC touchpoint anchor: BHist UnaryHistory Cont ProbeBundle Pkg PkgSig hsame
  intro carrier basePkg
  obtain ⟨baseUnary, displayedUnary, arrowUnary, _fiberUnary, _transportUnary,
    _routeUnary, _provenanceUnary, _localNameUnary, displayedArrowBase,
    routeProvenanceLocalName, localNamePkg, transportArrow⟩ := carrier
  exact
    ⟨baseUnary, displayedUnary, arrowUnary, displayedArrowBase, routeProvenanceLocalName,
      transportArrow, localNamePkg, basePkg⟩

end BEDC.Derived.SliceCategoryUp
