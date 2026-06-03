import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.CellularPatternCatalogUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def CellularPatternCatalogCarrier [AskSetup] [PackageSetup]
    (R W T G H C P N ruleWindowRead catalogRead tagRead : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  UnaryHistory R ∧ UnaryHistory W ∧ UnaryHistory G ∧ UnaryHistory T ∧
    Cont R W ruleWindowRead ∧ Cont ruleWindowRead G catalogRead ∧
      Cont catalogRead T tagRead ∧ PkgSig bundle P pkg ∧ PkgSig bundle N pkg

theorem CellularPatternCatalogCarrier_route_closure [AskSetup] [PackageSetup]
    {R W T G H C P N ruleWindowRead catalogRead tagRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CellularPatternCatalogCarrier R W T G H C P N ruleWindowRead catalogRead tagRead
        bundle pkg →
      UnaryHistory ruleWindowRead ∧ UnaryHistory catalogRead ∧ UnaryHistory tagRead ∧
        PkgSig bundle P pkg ∧ PkgSig bundle N pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig UnaryHistory
  intro carrier
  obtain ⟨unaryR, unaryW, unaryG, unaryT, ruleWindowRoute, catalogRoute, tagRoute,
    pkgP, pkgN⟩ := carrier
  have ruleWindowUnary : UnaryHistory ruleWindowRead :=
    unary_cont_closed unaryR unaryW ruleWindowRoute
  have catalogUnary : UnaryHistory catalogRead :=
    unary_cont_closed ruleWindowUnary unaryG catalogRoute
  have tagUnary : UnaryHistory tagRead :=
    unary_cont_closed catalogUnary unaryT tagRoute
  exact ⟨ruleWindowUnary, catalogUnary, tagUnary, pkgP, pkgN⟩

end BEDC.Derived.CellularPatternCatalogUp
