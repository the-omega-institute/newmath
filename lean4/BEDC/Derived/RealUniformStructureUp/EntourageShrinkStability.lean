import BEDC.Derived.RealUniformStructureUp

namespace BEDC.Derived.RealUniformStructureUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem RealUniformStructureEntourageShrinkStability [AskSetup] [PackageSetup]
    {R M U F D S Q H C P N endpointRead radiusRead shrinkRead windowRead
      readbackRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    RealUniformStructureCarrier R M U F D S Q H C P N bundle pkg ->
      Cont R M endpointRead ->
        Cont endpointRead D radiusRead ->
          Cont radiusRead D shrinkRead ->
            Cont shrinkRead S windowRead ->
              Cont windowRead Q readbackRead ->
                PkgSig bundle readbackRead pkg ->
                  UnaryHistory shrinkRead ∧ UnaryHistory windowRead ∧
                    UnaryHistory readbackRead ∧ PkgSig bundle P pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig UnaryHistory
  intro carrier endpointCont radiusCont shrinkCont windowCont readbackCont _readbackPkg
  have rUnary : UnaryHistory R := carrier.left
  have mUnary : UnaryHistory M := carrier.right.left
  have dUnary : UnaryHistory D := carrier.right.right.right.right.left
  have sUnary : UnaryHistory S := carrier.right.right.right.right.right.left
  have qUnary : UnaryHistory Q := carrier.right.right.right.right.right.right.left
  have pPkg : PkgSig bundle P pkg :=
    carrier.right.right.right.right.right.right.right.right.right.right.right
  have endpointUnary : UnaryHistory endpointRead :=
    unary_cont_closed rUnary mUnary endpointCont
  have radiusUnary : UnaryHistory radiusRead :=
    unary_cont_closed endpointUnary dUnary radiusCont
  have shrinkUnary : UnaryHistory shrinkRead :=
    unary_cont_closed radiusUnary dUnary shrinkCont
  have windowUnary : UnaryHistory windowRead :=
    unary_cont_closed shrinkUnary sUnary windowCont
  have readbackUnary : UnaryHistory readbackRead :=
    unary_cont_closed windowUnary qUnary readbackCont
  exact ⟨shrinkUnary, windowUnary, readbackUnary, pPkg⟩

end BEDC.Derived.RealUniformStructureUp
