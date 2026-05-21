import BEDC.Derived.AuthorizedGeneratorRecursorUp.L10Carrier

namespace BEDC.Derived.AuthorizedGeneratorRecursorUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem AuthorizedGeneratorRecursorOutputBoundaryNonescape [AskSetup] [PackageSetup]
    {I E M B D O A H C P G N outputRead publicRead boundaryRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    AuthorizedGeneratorRecursorCarrier I E M B D O A H C P G N bundle pkg ->
      Cont D O outputRead ->
        Cont outputRead C publicRead ->
          Cont G N boundaryRead ->
            PkgSig bundle publicRead pkg ->
              UnaryHistory O ∧ UnaryHistory outputRead ∧ UnaryHistory publicRead ∧
                Cont D O outputRead ∧ Cont outputRead C publicRead ∧
                  Cont G N boundaryRead ∧ hsame H (append A C) ∧
                    PkgSig bundle P pkg ∧ PkgSig bundle publicRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg UnaryHistory Cont PkgSig hsame
  intro carrier outputRoute publicRoute boundaryRoute publicPkg
  rcases carrier with
    ⟨_unaryI, _unaryE, _unaryM, _unaryB, unaryD, unaryO, _unaryA, _unaryH,
      unaryC, _unaryP, unaryG, unaryN, _contIEM, _contMBD, _contDOA,
      transportSame, provenancePkg⟩
  have outputReadUnary : UnaryHistory outputRead :=
    unary_cont_closed unaryD unaryO outputRoute
  have publicReadUnary : UnaryHistory publicRead :=
    unary_cont_closed outputReadUnary unaryC publicRoute
  exact
    ⟨unaryO, outputReadUnary, publicReadUnary, outputRoute, publicRoute, boundaryRoute,
      transportSame, provenancePkg, publicPkg⟩

end BEDC.Derived.AuthorizedGeneratorRecursorUp
