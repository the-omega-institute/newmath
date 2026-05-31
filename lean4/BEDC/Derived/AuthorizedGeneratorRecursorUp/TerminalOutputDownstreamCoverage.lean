import BEDC.Derived.AuthorizedGeneratorRecursorUp.L10Carrier

namespace BEDC.Derived.AuthorizedGeneratorRecursorUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem AuthorizedGeneratorRecursorTerminalOutputDownstreamCoverage [AskSetup] [PackageSetup]
    {I E M B D O A H C P G N outputRead continuationRead provenanceRead terminalRead
      ledgerRead downstreamRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    AuthorizedGeneratorRecursorCarrier I E M B D O A H C P G N bundle pkg ->
      Cont O A outputRead ->
        Cont outputRead C continuationRead ->
          Cont continuationRead P provenanceRead ->
            Cont provenanceRead N terminalRead ->
              Cont terminalRead G ledgerRead ->
                Cont ledgerRead N downstreamRead ->
                  PkgSig bundle downstreamRead pkg ->
                    UnaryHistory O ∧ UnaryHistory A ∧ UnaryHistory C ∧ UnaryHistory P ∧
                      UnaryHistory G ∧ UnaryHistory N ∧ UnaryHistory outputRead ∧
                        UnaryHistory continuationRead ∧ UnaryHistory provenanceRead ∧
                          UnaryHistory terminalRead ∧ UnaryHistory ledgerRead ∧
                            UnaryHistory downstreamRead ∧ Cont O A outputRead ∧
                              Cont outputRead C continuationRead ∧
                                Cont continuationRead P provenanceRead ∧
                                  Cont provenanceRead N terminalRead ∧
                                    Cont terminalRead G ledgerRead ∧
                                      Cont ledgerRead N downstreamRead ∧
                                        hsame H (append A C) ∧ PkgSig bundle P pkg ∧
                                          PkgSig bundle downstreamRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg UnaryHistory Cont PkgSig hsame
  intro carrier outputCont continuationCont provenanceCont terminalCont ledgerCont
    downstreamCont downstreamPkg
  rcases carrier with
    ⟨_unaryI, _unaryE, _unaryM, _unaryB, _unaryD, unaryO, unaryA, _unaryH,
      unaryC, unaryP, unaryG, unaryN, _contIEM, _contMBD, _contDOA,
      sameTransport, provenancePkg⟩
  have outputUnary : UnaryHistory outputRead :=
    unary_cont_closed unaryO unaryA outputCont
  have continuationUnary : UnaryHistory continuationRead :=
    unary_cont_closed outputUnary unaryC continuationCont
  have provenanceUnary : UnaryHistory provenanceRead :=
    unary_cont_closed continuationUnary unaryP provenanceCont
  have terminalUnary : UnaryHistory terminalRead :=
    unary_cont_closed provenanceUnary unaryN terminalCont
  have ledgerUnary : UnaryHistory ledgerRead :=
    unary_cont_closed terminalUnary unaryG ledgerCont
  have downstreamUnary : UnaryHistory downstreamRead :=
    unary_cont_closed ledgerUnary unaryN downstreamCont
  exact
    ⟨unaryO, unaryA, unaryC, unaryP, unaryG, unaryN, outputUnary, continuationUnary,
      provenanceUnary, terminalUnary, ledgerUnary, downstreamUnary, outputCont,
      continuationCont, provenanceCont, terminalCont, ledgerCont, downstreamCont,
      sameTransport, provenancePkg, downstreamPkg⟩

end BEDC.Derived.AuthorizedGeneratorRecursorUp
