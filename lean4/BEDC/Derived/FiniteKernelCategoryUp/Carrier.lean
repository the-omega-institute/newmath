import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Package
import BEDC.FKernel.Unary
import BEDC.Derived.FiniteKernelCategoryUp.TasteGate

namespace BEDC.Derived.FiniteKernelCategoryUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem FiniteKernelCategoryCarrier_object_hom_boundary [AskSetup] [PackageSetup]
    {objectRow homRow identityRow compositionRow associativityRow unitRow transportRow
      routeRow provenanceRow nameCertRow objectRead homRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    UnaryHistory objectRow →
      UnaryHistory homRow →
        Cont objectRow homRow homRead →
          PkgSig bundle objectRead pkg →
            PkgSig bundle homRead pkg →
              (∃ packet : FiniteKernelCategoryUp,
                packet =
                  FiniteKernelCategoryUp.mk objectRow homRow identityRow compositionRow
                    associativityRow unitRow transportRow routeRow provenanceRow nameCertRow) ∧
                UnaryHistory objectRow ∧ UnaryHistory homRow ∧
                  Cont objectRow homRow homRead ∧ PkgSig bundle objectRead pkg ∧
                    PkgSig bundle homRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg UnaryHistory Cont PkgSig
  intro objectUnary homUnary homRoute objectPkg homPkg
  exact
    ⟨Exists.intro
      (FiniteKernelCategoryUp.mk objectRow homRow identityRow compositionRow associativityRow
        unitRow transportRow routeRow provenanceRow nameCertRow) rfl,
      objectUnary, homUnary, homRoute, objectPkg, homPkg⟩

end BEDC.Derived.FiniteKernelCategoryUp
