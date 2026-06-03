import BEDC.Derived.RealUniformStructureUp

namespace BEDC.Derived.RealUniformStructureUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem RealUniformStructureRealEqualityFilterBoundary [AskSetup] [PackageSetup]
    {R M U F D S Q H C P N equalityRead filterRead sealRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    RealUniformStructureCarrier R M U F D S Q H C P N bundle pkg →
      Cont Q U equalityRead →
        Cont equalityRead F filterRead →
          Cont filterRead R sealRead →
            PkgSig bundle sealRead pkg →
              UnaryHistory equalityRead ∧ UnaryHistory filterRead ∧ UnaryHistory sealRead ∧
                Cont Q U equalityRead ∧ Cont equalityRead F filterRead ∧
                  Cont filterRead R sealRead ∧ PkgSig bundle P pkg ∧
                    PkgSig bundle sealRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig UnaryHistory
  intro carrier equalityCont filterCont sealCont sealPkg
  have rUnary : UnaryHistory R := carrier.left
  have uUnary : UnaryHistory U := carrier.right.right.left
  have fUnary : UnaryHistory F := carrier.right.right.right.left
  have qUnary : UnaryHistory Q := carrier.right.right.right.right.right.right.left
  have pPkg : PkgSig bundle P pkg :=
    carrier.right.right.right.right.right.right.right.right.right.right.right
  have equalityUnary : UnaryHistory equalityRead :=
    unary_cont_closed qUnary uUnary equalityCont
  have filterUnary : UnaryHistory filterRead :=
    unary_cont_closed equalityUnary fUnary filterCont
  have sealUnary : UnaryHistory sealRead :=
    unary_cont_closed filterUnary rUnary sealCont
  exact
    ⟨equalityUnary, filterUnary, sealUnary, equalityCont, filterCont, sealCont, pPkg,
      sealPkg⟩

end BEDC.Derived.RealUniformStructureUp
