import BEDC.Derived.ContinuationMonadUp

namespace BEDC.Derived.ContinuationMonadUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem ContinuationMonadCarrier_root_formal_public_readback_terminality
    [AskSetup] [PackageSetup]
    {A B C f g u H K L N category generator publicRead formalRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ContinuationMonadCarrier A B C f g u H K L N ->
      Cont L N category ->
        Cont category N generator ->
          Cont generator N publicRead ->
            Cont publicRead N formalRead ->
              PkgSig bundle formalRead pkg ->
                UnaryHistory A ∧ UnaryHistory B ∧ UnaryHistory C ∧ UnaryHistory f ∧
                  UnaryHistory g ∧ UnaryHistory u ∧ UnaryHistory K ∧ UnaryHistory L ∧
                    UnaryHistory category ∧ UnaryHistory generator ∧
                      UnaryHistory publicRead ∧ UnaryHistory formalRead ∧
                        Cont A f B ∧ Cont B g C ∧ Cont f g K ∧ Cont K u L ∧
                          Cont L N category ∧ Cont category N generator ∧
                            Cont generator N publicRead ∧ Cont publicRead N formalRead ∧
                              hsame N L ∧ PkgSig bundle formalRead pkg := by
  -- BEDC touchpoint anchor: BHist AskSetup PackageSetup ProbeBundle Pkg Cont hsame
  intro carrier categoryRoute generatorRoute publicRoute formalRoute formalPkg
  obtain ⟨unaryA, unaryF, unaryG, unaryU, routeB, routeC, routeK, routeL,
    sameEndpoint⟩ := carrier
  have unaryB : UnaryHistory B :=
    unary_cont_closed unaryA unaryF routeB
  have unaryC : UnaryHistory C :=
    unary_cont_closed unaryB unaryG routeC
  have unaryK : UnaryHistory K :=
    unary_cont_closed unaryF unaryG routeK
  have unaryL : UnaryHistory L :=
    unary_cont_closed unaryK unaryU routeL
  have unaryN : UnaryHistory N :=
    unary_transport unaryL (hsame_symm sameEndpoint)
  have unaryCategory : UnaryHistory category :=
    unary_cont_closed unaryL unaryN categoryRoute
  have unaryGenerator : UnaryHistory generator :=
    unary_cont_closed unaryCategory unaryN generatorRoute
  have unaryPublicRead : UnaryHistory publicRead :=
    unary_cont_closed unaryGenerator unaryN publicRoute
  have unaryFormalRead : UnaryHistory formalRead :=
    unary_cont_closed unaryPublicRead unaryN formalRoute
  exact
    ⟨unaryA, unaryB, unaryC, unaryF, unaryG, unaryU, unaryK, unaryL, unaryCategory,
      unaryGenerator, unaryPublicRead, unaryFormalRead, routeB, routeC, routeK, routeL,
      categoryRoute, generatorRoute, publicRoute, formalRoute, sameEndpoint, formalPkg⟩

end BEDC.Derived.ContinuationMonadUp
