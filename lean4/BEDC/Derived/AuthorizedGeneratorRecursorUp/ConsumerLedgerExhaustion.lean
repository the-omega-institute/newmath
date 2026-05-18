import BEDC.Derived.AuthorizedGeneratorRecursorUp.L10Carrier

namespace BEDC.Derived.AuthorizedGeneratorRecursorUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem AuthorizedGeneratorRecursor_consumer_ledger_exhaustion [AskSetup] [PackageSetup]
    {I E M B D O A H C P G N outputRead tailRead ledgerRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    AuthorizedGeneratorRecursorCarrier I E M B D O A H C P G N bundle pkg ->
      Cont O A outputRead ->
        Cont outputRead C tailRead ->
          Cont tailRead N ledgerRead ->
            PkgSig bundle ledgerRead pkg ->
              UnaryHistory O ∧ UnaryHistory A ∧ UnaryHistory C ∧ UnaryHistory outputRead ∧
                UnaryHistory tailRead ∧ UnaryHistory ledgerRead ∧ Cont O A outputRead ∧
                  Cont outputRead C tailRead ∧ Cont tailRead N ledgerRead ∧
                    PkgSig bundle P pkg ∧ PkgSig bundle ledgerRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg UnaryHistory Cont PkgSig
  intro carrier outputRoute tailRoute ledgerRoute ledgerPkg
  rcases carrier with
    ⟨_unaryI, _unaryE, _unaryM, _unaryB, _unaryD, unaryO, unaryA, _unaryH, unaryC,
      unaryP, _unaryG, unaryN, _contIEM, _contMBD, _contDOA, _sameTransport,
      provenancePkg⟩
  have outputUnary : UnaryHistory outputRead :=
    unary_cont_closed unaryO unaryA outputRoute
  have tailUnary : UnaryHistory tailRead :=
    unary_cont_closed outputUnary unaryC tailRoute
  have ledgerUnary : UnaryHistory ledgerRead :=
    unary_cont_closed tailUnary unaryN ledgerRoute
  exact
    ⟨unaryO, unaryA, unaryC, outputUnary, tailUnary, ledgerUnary, outputRoute,
      tailRoute, ledgerRoute, provenancePkg, ledgerPkg⟩

end BEDC.Derived.AuthorizedGeneratorRecursorUp
