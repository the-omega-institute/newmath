import BEDC.Derived.AuthorizedGeneratorRecursorUp.L10Carrier

namespace BEDC.Derived.AuthorizedGeneratorRecursorUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem AuthorizedGeneratorRecursorStreamNameFiniteRequestPublicity [AskSetup] [PackageSetup]
    {I E M B D O A H C P G N requestRead publicRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    AuthorizedGeneratorRecursorCarrier I E M B D O A H C P G N bundle pkg ->
      Cont O C requestRead ->
        Cont requestRead N publicRead ->
          PkgSig bundle publicRead pkg ->
            UnaryHistory I ∧ UnaryHistory E ∧ UnaryHistory M ∧ UnaryHistory B ∧
              UnaryHistory D ∧ UnaryHistory O ∧ UnaryHistory A ∧ UnaryHistory C ∧
                UnaryHistory G ∧ UnaryHistory N ∧ UnaryHistory requestRead ∧
                  UnaryHistory publicRead ∧ Cont O C requestRead ∧
                    Cont requestRead N publicRead ∧ PkgSig bundle P pkg ∧
                      PkgSig bundle publicRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg UnaryHistory Cont PkgSig hsame
  intro carrier requestCont publicCont publicPkg
  rcases carrier with
    ⟨unaryI, unaryE, unaryM, unaryB, unaryD, unaryO, unaryA, _unaryH, unaryC,
      _unaryP, unaryG, unaryN, _contIEM, _contMBD, _contDOA, _sameTransport,
      provenancePkg⟩
  have requestUnary : UnaryHistory requestRead :=
    unary_cont_closed unaryO unaryC requestCont
  have publicUnary : UnaryHistory publicRead :=
    unary_cont_closed requestUnary unaryN publicCont
  exact
    ⟨unaryI, unaryE, unaryM, unaryB, unaryD, unaryO, unaryA, unaryC, unaryG, unaryN,
      requestUnary, publicUnary, requestCont, publicCont, provenancePkg, publicPkg⟩

end BEDC.Derived.AuthorizedGeneratorRecursorUp
