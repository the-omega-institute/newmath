import BEDC.Derived.AuthorizedGeneratorRecursorUp.L10Carrier

namespace BEDC.Derived.AuthorizedGeneratorRecursorUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem AuthorizedGeneratorRecursor_output_refusal [AskSetup] [PackageSetup]
    {I E M B D O A H C P G N outputRead boundaryRead refusalRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    AuthorizedGeneratorRecursorCarrier I E M B D O A H C P G N bundle pkg ->
      Cont O A outputRead ->
        Cont G N boundaryRead ->
          Cont boundaryRead A refusalRead ->
            PkgSig bundle refusalRead pkg ->
              UnaryHistory O ∧ UnaryHistory A ∧ UnaryHistory G ∧ UnaryHistory N ∧
                UnaryHistory outputRead ∧ UnaryHistory boundaryRead ∧
                  UnaryHistory refusalRead ∧ hsame H (append A C) ∧
                    Cont O A outputRead ∧ Cont G N boundaryRead ∧
                      Cont boundaryRead A refusalRead ∧ PkgSig bundle P pkg ∧
                        PkgSig bundle refusalRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg UnaryHistory Cont PkgSig hsame
  intro carrier outputRoute boundaryRoute refusalRoute refusalPkg
  rcases carrier with
    ⟨_unaryI, _unaryE, _unaryM, _unaryB, _unaryD, unaryO, unaryA, _unaryH, unaryC,
      unaryP, unaryG, unaryN, _contIEM, _contMBD, _contDOA, sameTransport,
      provenancePkg⟩
  have outputUnary : UnaryHistory outputRead :=
    unary_cont_closed unaryO unaryA outputRoute
  have boundaryUnary : UnaryHistory boundaryRead :=
    unary_cont_closed unaryG unaryN boundaryRoute
  have refusalUnary : UnaryHistory refusalRead :=
    unary_cont_closed boundaryUnary unaryA refusalRoute
  exact
    ⟨unaryO, unaryA, unaryG, unaryN, outputUnary, boundaryUnary, refusalUnary,
      sameTransport, outputRoute, boundaryRoute, refusalRoute, provenancePkg, refusalPkg⟩

end BEDC.Derived.AuthorizedGeneratorRecursorUp
