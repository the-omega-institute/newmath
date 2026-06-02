import BEDC.Derived.RealUniformStructureUp

namespace BEDC.Derived.RealUniformStructureUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem RealUniformStructurePositiveRadiusEntourageRefinement [AskSetup] [PackageSetup]
    {R M U F D S Q H C P N distanceRead radiusRead refinedRadiusRead refinedBasisRead
      cauchyRead windowRead readbackRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    RealUniformStructureCarrier R M U F D S Q H C P N bundle pkg ->
      Cont R M distanceRead ->
        Cont distanceRead D radiusRead ->
          Cont radiusRead D refinedRadiusRead ->
            Cont refinedRadiusRead U refinedBasisRead ->
              Cont refinedBasisRead F cauchyRead ->
                Cont cauchyRead S windowRead ->
                  Cont windowRead Q readbackRead ->
                    PkgSig bundle readbackRead pkg ->
                      UnaryHistory refinedRadiusRead ∧ UnaryHistory refinedBasisRead ∧
                        UnaryHistory cauchyRead ∧ UnaryHistory windowRead ∧
                          UnaryHistory readbackRead ∧ Cont distanceRead D radiusRead ∧
                            Cont radiusRead D refinedRadiusRead ∧
                              Cont refinedRadiusRead U refinedBasisRead ∧
                                Cont refinedBasisRead F cauchyRead ∧
                                  Cont cauchyRead S windowRead ∧
                                    Cont windowRead Q readbackRead ∧
                                      PkgSig bundle P pkg ∧
                                        PkgSig bundle readbackRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig UnaryHistory
  intro carrier distanceCont radiusCont refinedRadiusCont refinedBasisCont cauchyCont
    windowCont readbackCont readbackPkg
  have rUnary : UnaryHistory R := carrier.left
  have mUnary : UnaryHistory M := carrier.right.left
  have uUnary : UnaryHistory U := carrier.right.right.left
  have fUnary : UnaryHistory F := carrier.right.right.right.left
  have dUnary : UnaryHistory D := carrier.right.right.right.right.left
  have sUnary : UnaryHistory S := carrier.right.right.right.right.right.left
  have qUnary : UnaryHistory Q := carrier.right.right.right.right.right.right.left
  have pPkg : PkgSig bundle P pkg :=
    carrier.right.right.right.right.right.right.right.right.right.right.right
  have distanceUnary : UnaryHistory distanceRead :=
    unary_cont_closed rUnary mUnary distanceCont
  have radiusUnary : UnaryHistory radiusRead :=
    unary_cont_closed distanceUnary dUnary radiusCont
  have refinedRadiusUnary : UnaryHistory refinedRadiusRead :=
    unary_cont_closed radiusUnary dUnary refinedRadiusCont
  have refinedBasisUnary : UnaryHistory refinedBasisRead :=
    unary_cont_closed refinedRadiusUnary uUnary refinedBasisCont
  have cauchyUnary : UnaryHistory cauchyRead :=
    unary_cont_closed refinedBasisUnary fUnary cauchyCont
  have windowUnary : UnaryHistory windowRead :=
    unary_cont_closed cauchyUnary sUnary windowCont
  have readbackUnary : UnaryHistory readbackRead :=
    unary_cont_closed windowUnary qUnary readbackCont
  exact
    ⟨refinedRadiusUnary, refinedBasisUnary, cauchyUnary, windowUnary, readbackUnary,
      radiusCont, refinedRadiusCont, refinedBasisCont, cauchyCont, windowCont,
      readbackCont, pPkg, readbackPkg⟩

end BEDC.Derived.RealUniformStructureUp
