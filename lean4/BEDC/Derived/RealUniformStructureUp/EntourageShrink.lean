import BEDC.Derived.RealUniformStructureUp

namespace BEDC.Derived.RealUniformStructureUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def RealUniformStructureEntourageShrink [AskSetup] [PackageSetup]
    (R M U F D S Q H C P N radiusRead shrinkRead windowRead generatedRead cauchyRead :
      BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  RealUniformStructureCarrier R M U F D S Q H C P N bundle pkg ∧
    Cont R M radiusRead ∧
      Cont radiusRead D shrinkRead ∧
        Cont shrinkRead S windowRead ∧
          Cont windowRead U generatedRead ∧
            Cont generatedRead F cauchyRead ∧ PkgSig bundle cauchyRead pkg

theorem RealUniformStructureEntourageShrink_route_closure [AskSetup] [PackageSetup]
    {R M U F D S Q H C P N radiusRead shrinkRead windowRead generatedRead cauchyRead :
      BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    RealUniformStructureEntourageShrink R M U F D S Q H C P N radiusRead shrinkRead
        windowRead generatedRead cauchyRead bundle pkg →
      UnaryHistory shrinkRead ∧
        UnaryHistory windowRead ∧
          UnaryHistory generatedRead ∧
            UnaryHistory cauchyRead ∧
              PkgSig bundle P pkg ∧ PkgSig bundle cauchyRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig UnaryHistory
  intro shrink
  have carrier :
      RealUniformStructureCarrier R M U F D S Q H C P N bundle pkg :=
    shrink.left
  have rUnary : UnaryHistory R := carrier.left
  have mUnary : UnaryHistory M := carrier.right.left
  have uUnary : UnaryHistory U := carrier.right.right.left
  have fUnary : UnaryHistory F := carrier.right.right.right.left
  have dUnary : UnaryHistory D := carrier.right.right.right.right.left
  have sUnary : UnaryHistory S := carrier.right.right.right.right.right.left
  have pPkg : PkgSig bundle P pkg :=
    carrier.right.right.right.right.right.right.right.right.right.right.right
  have radiusCont : Cont R M radiusRead := shrink.right.left
  have shrinkCont : Cont radiusRead D shrinkRead := shrink.right.right.left
  have windowCont : Cont shrinkRead S windowRead := shrink.right.right.right.left
  have generatedCont : Cont windowRead U generatedRead :=
    shrink.right.right.right.right.left
  have cauchyCont : Cont generatedRead F cauchyRead :=
    shrink.right.right.right.right.right.left
  have cauchyPkg : PkgSig bundle cauchyRead pkg :=
    shrink.right.right.right.right.right.right
  have radiusUnary : UnaryHistory radiusRead :=
    unary_cont_closed rUnary mUnary radiusCont
  have shrinkUnary : UnaryHistory shrinkRead :=
    unary_cont_closed radiusUnary dUnary shrinkCont
  have windowUnary : UnaryHistory windowRead :=
    unary_cont_closed shrinkUnary sUnary windowCont
  have generatedUnary : UnaryHistory generatedRead :=
    unary_cont_closed windowUnary uUnary generatedCont
  have cauchyUnary : UnaryHistory cauchyRead :=
    unary_cont_closed generatedUnary fUnary cauchyCont
  exact ⟨shrinkUnary, windowUnary, generatedUnary, cauchyUnary, pPkg, cauchyPkg⟩

end BEDC.Derived.RealUniformStructureUp
