import BEDC.Derived.AuthorizedGeneratorRecursorUp.L10Carrier

namespace BEDC.Derived.AuthorizedGeneratorRecursorUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem AuthorizedGeneratorRecursorOutputRouteStrictLocalObstruction
    [AskSetup] [PackageSetup]
    {I E M B D O A H C P G N publicRead boundaryRead obstructionRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    AuthorizedGeneratorRecursorCarrier I E M B D O A H C P G N bundle pkg ->
      Cont O A publicRead ->
        Cont G N boundaryRead ->
          Cont publicRead boundaryRead obstructionRead ->
            PkgSig bundle obstructionRead pkg ->
              UnaryHistory publicRead ∧ UnaryHistory boundaryRead ∧
                UnaryHistory obstructionRead ∧ Cont O A publicRead ∧
                  Cont G N boundaryRead ∧ Cont publicRead boundaryRead obstructionRead ∧
                    hsame H (append A C) ∧ PkgSig bundle P pkg ∧
                      PkgSig bundle obstructionRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg PkgSig Cont UnaryHistory hsame
  intro carrier publicRoute boundaryRoute obstructionRoute obstructionPkg
  rcases carrier with
    ⟨_unaryI, _unaryE, _unaryM, _unaryB, _unaryD, unaryO, unaryA, _unaryH,
      _unaryC, _unaryP, unaryG, unaryN, _contIEM, _contMBD, _contDOA, transportSame,
      provenancePkg⟩
  have publicUnary : UnaryHistory publicRead :=
    unary_cont_closed unaryO unaryA publicRoute
  have boundaryUnary : UnaryHistory boundaryRead :=
    unary_cont_closed unaryG unaryN boundaryRoute
  have obstructionUnary : UnaryHistory obstructionRead :=
    unary_cont_closed publicUnary boundaryUnary obstructionRoute
  exact
    ⟨publicUnary, boundaryUnary, obstructionUnary, publicRoute, boundaryRoute,
      obstructionRoute, transportSame, provenancePkg, obstructionPkg⟩

end BEDC.Derived.AuthorizedGeneratorRecursorUp
