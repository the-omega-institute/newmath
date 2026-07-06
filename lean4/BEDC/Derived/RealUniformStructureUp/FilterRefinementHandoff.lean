import BEDC.Derived.RealUniformStructureUp

namespace BEDC.Derived.RealUniformStructureUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem RealUniformStructureCarrier_filter_refinement_handoff [AskSetup] [PackageSetup]
    {R M U F D S Q H C P N distanceRead radiusRead basisRead cauchyRead refinedRead :
      BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    RealUniformStructureCarrier R M U F D S Q H C P N bundle pkg ->
      Cont R M distanceRead ->
        Cont distanceRead D radiusRead ->
          Cont radiusRead U basisRead ->
            Cont basisRead F cauchyRead ->
              Cont cauchyRead H refinedRead ->
                PkgSig bundle refinedRead pkg ->
                  UnaryHistory R ∧ UnaryHistory M ∧ UnaryHistory D ∧ UnaryHistory U ∧
                    UnaryHistory F ∧ UnaryHistory H ∧ UnaryHistory distanceRead ∧
                      UnaryHistory radiusRead ∧ UnaryHistory basisRead ∧
                        UnaryHistory cauchyRead ∧ UnaryHistory refinedRead ∧
                          Cont R M distanceRead ∧ Cont distanceRead D radiusRead ∧
                            Cont radiusRead U basisRead ∧ Cont basisRead F cauchyRead ∧
                              Cont cauchyRead H refinedRead ∧ PkgSig bundle P pkg ∧
                                PkgSig bundle refinedRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig UnaryHistory
  intro carrier distanceCont radiusCont basisCont cauchyCont refinedCont refinedPkg
  have rUnary : UnaryHistory R := carrier.left
  have mUnary : UnaryHistory M := carrier.right.left
  have uUnary : UnaryHistory U := carrier.right.right.left
  have fUnary : UnaryHistory F := carrier.right.right.right.left
  have dUnary : UnaryHistory D := carrier.right.right.right.right.left
  have hUnary : UnaryHistory H := carrier.right.right.right.right.right.right.right.left
  have pPkg : PkgSig bundle P pkg :=
    carrier.right.right.right.right.right.right.right.right.right.right.right
  have distanceUnary : UnaryHistory distanceRead :=
    unary_cont_closed rUnary mUnary distanceCont
  have radiusUnary : UnaryHistory radiusRead :=
    unary_cont_closed distanceUnary dUnary radiusCont
  have basisUnary : UnaryHistory basisRead :=
    unary_cont_closed radiusUnary uUnary basisCont
  have cauchyUnary : UnaryHistory cauchyRead :=
    unary_cont_closed basisUnary fUnary cauchyCont
  have refinedUnary : UnaryHistory refinedRead :=
    unary_cont_closed cauchyUnary hUnary refinedCont
  exact
    ⟨rUnary, mUnary, dUnary, uUnary, fUnary, hUnary, distanceUnary, radiusUnary,
      basisUnary, cauchyUnary, refinedUnary, distanceCont, radiusCont, basisCont,
      cauchyCont, refinedCont, pPkg, refinedPkg⟩

end BEDC.Derived.RealUniformStructureUp
