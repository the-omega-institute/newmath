import BEDC.Derived.CategoryUp
import BEDC.Derived.ContinuationMonadUp
import BEDC.Derived.GeneratorClosureUp

namespace BEDC.Derived.ContinuationMonadUp

open BEDC.Derived.CategoryUp
open BEDC.Derived.GeneratorClosureUp
open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem ContinuationMonadCarrier_category_generator_formal_handoff [AskSetup] [PackageSetup]
    {A B C f g u H K L N category generator formal : BHist}
    {gen constructors authorized classifier witnesses transport routes provenance name endpoint :
      BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ContinuationMonadCarrier A B C f g u H K L N →
      CategoryHomCarrier A C L →
        GeneratorClosurePacket gen constructors authorized classifier witnesses transport routes
            provenance name endpoint bundle pkg →
          Cont L N category →
            Cont category K generator →
              Cont generator N formal →
                hsame endpoint generator →
                  PkgSig bundle formal pkg →
                    UnaryHistory A ∧ UnaryHistory C ∧ UnaryHistory L ∧
                      UnaryHistory category ∧ UnaryHistory generator ∧ UnaryHistory formal ∧
                        CategoryHomCarrier A C L ∧
                          GeneratorClosurePacket gen constructors authorized classifier witnesses
                            transport routes provenance name endpoint bundle pkg ∧
                            Cont L N category ∧ Cont category K generator ∧
                              Cont generator N formal ∧ hsame endpoint generator ∧
                                PkgSig bundle formal pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont UnaryHistory hsame
  intro carrier categoryHom generatorPacket categoryRoute generatorRoute formalRoute
    sameEndpointGenerator formalPkg
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
    unary_cont_closed unaryCategory unaryK generatorRoute
  have unaryFormal : UnaryHistory formal :=
    unary_cont_closed unaryGenerator unaryN formalRoute
  exact
    ⟨unaryA, unaryC, unaryL, unaryCategory, unaryGenerator, unaryFormal, categoryHom,
      generatorPacket, categoryRoute, generatorRoute, formalRoute, sameEndpointGenerator,
      formalPkg⟩

end BEDC.Derived.ContinuationMonadUp
