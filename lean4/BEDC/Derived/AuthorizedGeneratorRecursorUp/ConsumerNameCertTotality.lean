import BEDC.Derived.AuthorizedGeneratorRecursorUp.L10Carrier

namespace BEDC.Derived.AuthorizedGeneratorRecursorUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem AuthorizedGeneratorRecursorConsumerNameCertTotality [AskSetup] [PackageSetup]
    {I E M B D O A H C P G N outputRead auditRead boundaryRead closedRead
      normalRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    AuthorizedGeneratorRecursorCarrier I E M B D O A H C P G N bundle pkg ->
      Cont O A outputRead ->
        Cont outputRead N auditRead ->
          Cont G N boundaryRead ->
            Cont auditRead boundaryRead closedRead ->
              Cont closedRead C normalRead ->
                PkgSig bundle normalRead pkg ->
                  UnaryHistory outputRead ∧ UnaryHistory auditRead ∧
                    UnaryHistory boundaryRead ∧ UnaryHistory closedRead ∧
                      UnaryHistory normalRead ∧ Cont O A outputRead ∧
                        Cont outputRead N auditRead ∧ Cont G N boundaryRead ∧
                          Cont auditRead boundaryRead closedRead ∧
                            Cont closedRead C normalRead ∧ hsame H (append A C) ∧
                              PkgSig bundle P pkg ∧ PkgSig bundle normalRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg PkgSig Cont UnaryHistory hsame
  intro carrier outputRoute auditRoute boundaryRoute closedRoute normalRoute normalPkg
  rcases carrier with
    ⟨_unaryI, _unaryE, _unaryM, _unaryB, _unaryD, unaryO, unaryA, _unaryH,
      unaryC, _unaryP, unaryG, unaryN, _contIEM, _contMBD, _contDOA, transportSame,
      provenancePkg⟩
  have outputUnary : UnaryHistory outputRead :=
    unary_cont_closed unaryO unaryA outputRoute
  have auditUnary : UnaryHistory auditRead :=
    unary_cont_closed outputUnary unaryN auditRoute
  have boundaryUnary : UnaryHistory boundaryRead :=
    unary_cont_closed unaryG unaryN boundaryRoute
  have closedUnary : UnaryHistory closedRead :=
    unary_cont_closed auditUnary boundaryUnary closedRoute
  have normalUnary : UnaryHistory normalRead :=
    unary_cont_closed closedUnary unaryC normalRoute
  exact
    ⟨outputUnary, auditUnary, boundaryUnary, closedUnary, normalUnary, outputRoute,
      auditRoute, boundaryRoute, closedRoute, normalRoute, transportSame, provenancePkg,
      normalPkg⟩

end BEDC.Derived.AuthorizedGeneratorRecursorUp
