import BEDC.Derived.AuthorizedGeneratorRecursorUp.L10Carrier

namespace BEDC.Derived.AuthorizedGeneratorRecursorUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem AuthorizedGeneratorRecursorClosedSubstitutionGateRow [AskSetup] [PackageSetup]
    {I E M B D O A H C P G N outputRead closedRead budgetRead handoff : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    AuthorizedGeneratorRecursorCarrier I E M B D O A H C P G N bundle pkg ->
      Cont D O outputRead ->
        Cont outputRead G closedRead ->
          Cont closedRead N budgetRead ->
            Cont O A handoff ->
              PkgSig bundle budgetRead pkg ->
                PkgSig bundle handoff pkg ->
                  UnaryHistory closedRead ∧ UnaryHistory budgetRead ∧
                    UnaryHistory handoff ∧ hsame H (append A C) ∧ PkgSig bundle P pkg ∧
                      PkgSig bundle budgetRead pkg ∧ PkgSig bundle handoff pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg UnaryHistory Cont PkgSig hsame
  intro carrier outputRoute closedRoute budgetRoute handoffRoute budgetPkg handoffPkg
  obtain
    ⟨_unaryI, _unaryE, _unaryM, _unaryB, unaryD, unaryO, unaryA, _unaryH, unaryC,
      unaryP, unaryG, unaryN, _iem, _mbd, _doa, transportAuditContinuation,
      provenancePkg⟩ :=
      carrier
  have outputReadUnary : UnaryHistory outputRead :=
    unary_cont_closed unaryD unaryO outputRoute
  have closedReadUnary : UnaryHistory closedRead :=
    unary_cont_closed outputReadUnary unaryG closedRoute
  have budgetReadUnary : UnaryHistory budgetRead :=
    unary_cont_closed closedReadUnary unaryN budgetRoute
  have handoffUnary : UnaryHistory handoff :=
    unary_cont_closed unaryO unaryA handoffRoute
  exact
    ⟨closedReadUnary, budgetReadUnary, handoffUnary, transportAuditContinuation,
      provenancePkg, budgetPkg, handoffPkg⟩

end BEDC.Derived.AuthorizedGeneratorRecursorUp
