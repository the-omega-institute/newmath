import BEDC.Derived.AuthorizedGeneratorRecursorUp.L10Carrier

namespace BEDC.Derived.AuthorizedGeneratorRecursorUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem AuthorizedGeneratorRecursorCarrier_route_totality_lock
    [AskSetup] [PackageSetup]
    {I E M B D O A H C P G N routeRead boundaryRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    AuthorizedGeneratorRecursorCarrier I E M B D O A H C P G N bundle pkg →
      Cont H C routeRead →
        Cont routeRead G boundaryRead →
          PkgSig bundle boundaryRead pkg →
            UnaryHistory I ∧ UnaryHistory E ∧ UnaryHistory M ∧ UnaryHistory B ∧
              UnaryHistory D ∧ UnaryHistory O ∧ UnaryHistory A ∧ UnaryHistory H ∧
                UnaryHistory C ∧ UnaryHistory P ∧ UnaryHistory G ∧ UnaryHistory N ∧
                  UnaryHistory routeRead ∧ UnaryHistory boundaryRead ∧ Cont I E M ∧
                    Cont M B D ∧ Cont D O A ∧ hsame H (append A C) ∧
                      Cont H C routeRead ∧ Cont routeRead G boundaryRead ∧
                        PkgSig bundle P pkg ∧ PkgSig bundle boundaryRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg UnaryHistory Cont PkgSig hsame
  intro carrier routeCont boundaryCont boundaryPkg
  rcases carrier with
    ⟨unaryI, unaryE, unaryM, unaryB, unaryD, unaryO, unaryA, unaryH, unaryC, unaryP,
      unaryG, unaryN, contIEM, contMBD, contDOA, sameTransport, provenancePkg⟩
  have routeUnary : UnaryHistory routeRead :=
    unary_cont_closed unaryH unaryC routeCont
  have boundaryUnary : UnaryHistory boundaryRead :=
    unary_cont_closed routeUnary unaryG boundaryCont
  exact
    ⟨unaryI, unaryE, unaryM, unaryB, unaryD, unaryO, unaryA, unaryH, unaryC, unaryP,
      unaryG, unaryN, routeUnary, boundaryUnary, contIEM, contMBD, contDOA,
      sameTransport, routeCont, boundaryCont, provenancePkg, boundaryPkg⟩

end BEDC.Derived.AuthorizedGeneratorRecursorUp
