import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Package.Core
import BEDC.FKernel.Unary.History

namespace BEDC.Derived

def RealUniformStructureUp : Type :=
  Unit

end BEDC.Derived

namespace BEDC.Derived.RealUniformStructureUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def RealUniformStructureCarrier [AskSetup] [PackageSetup]
    (R M U F D S Q H C P N : BHist) (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  UnaryHistory R ∧
    UnaryHistory M ∧
      UnaryHistory U ∧
        UnaryHistory F ∧
          UnaryHistory D ∧
            UnaryHistory S ∧
              UnaryHistory Q ∧
                UnaryHistory H ∧
                  UnaryHistory C ∧
                    UnaryHistory P ∧
                      UnaryHistory N ∧ PkgSig bundle P pkg

theorem RealUniformStructureCarrier_metric_uniformity_handoff [AskSetup] [PackageSetup]
    {R M U F D S Q H C P N radiusRead entourageRead filterRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    RealUniformStructureCarrier R M U F D S Q H C P N bundle pkg →
      Cont R M radiusRead →
        Cont radiusRead D entourageRead →
          Cont entourageRead U filterRead →
            PkgSig bundle filterRead pkg →
              UnaryHistory R ∧ UnaryHistory M ∧ UnaryHistory radiusRead ∧
                UnaryHistory entourageRead ∧ UnaryHistory filterRead ∧
                  Cont R M radiusRead ∧ Cont radiusRead D entourageRead ∧
                    Cont entourageRead U filterRead ∧ PkgSig bundle P pkg ∧
                      PkgSig bundle filterRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig UnaryHistory
  intro carrier radiusCont entourageCont filterCont filterPkg
  have rUnary : UnaryHistory R := carrier.left
  have mUnary : UnaryHistory M := carrier.right.left
  have uUnary : UnaryHistory U := carrier.right.right.left
  have dUnary : UnaryHistory D := carrier.right.right.right.right.left
  have pPkg : PkgSig bundle P pkg :=
    carrier.right.right.right.right.right.right.right.right.right.right.right
  have radiusUnary : UnaryHistory radiusRead :=
    unary_cont_closed rUnary mUnary radiusCont
  have entourageUnary : UnaryHistory entourageRead :=
    unary_cont_closed radiusUnary dUnary entourageCont
  have filterUnary : UnaryHistory filterRead :=
    unary_cont_closed entourageUnary uUnary filterCont
  exact
    ⟨rUnary, mUnary, radiusUnary, entourageUnary, filterUnary, radiusCont,
      entourageCont, filterCont, pPkg, filterPkg⟩

end BEDC.Derived.RealUniformStructureUp
