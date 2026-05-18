import BEDC.Derived.AuthorizedGeneratorRecursorUp.L10Carrier

namespace BEDC.Derived.AuthorizedGeneratorRecursorUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem AuthorizedGeneratorRecursorTerminalOutputReadbackPacket [AskSetup] [PackageSetup]
    {I E M B D O A H C P G N outputRead continuationRead provenanceRead terminalRead :
      BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    AuthorizedGeneratorRecursorCarrier I E M B D O A H C P G N bundle pkg ->
      Cont O A outputRead ->
        Cont outputRead C continuationRead ->
          Cont continuationRead P provenanceRead ->
            Cont provenanceRead N terminalRead ->
              PkgSig bundle terminalRead pkg ->
                UnaryHistory O ∧ UnaryHistory A ∧ UnaryHistory C ∧ UnaryHistory P ∧
                  UnaryHistory N ∧ UnaryHistory outputRead ∧ UnaryHistory continuationRead ∧
                    UnaryHistory provenanceRead ∧ UnaryHistory terminalRead ∧
                      Cont O A outputRead ∧ Cont outputRead C continuationRead ∧
                        Cont continuationRead P provenanceRead ∧
                          Cont provenanceRead N terminalRead ∧ hsame H (append A C) ∧
                            PkgSig bundle P pkg ∧ PkgSig bundle terminalRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg UnaryHistory Cont PkgSig hsame
  intro carrier outputCont continuationCont provenanceCont terminalCont terminalPkg
  rcases carrier with
    ⟨_unaryI, _unaryE, _unaryM, _unaryB, _unaryD, unaryO, unaryA, _unaryH,
      unaryC, unaryP, _unaryG, unaryN, _contIEM, _contMBD, _contDOA,
      sameTransport, provenancePkg⟩
  have outputUnary : UnaryHistory outputRead :=
    unary_cont_closed unaryO unaryA outputCont
  have continuationUnary : UnaryHistory continuationRead :=
    unary_cont_closed outputUnary unaryC continuationCont
  have provenanceUnary : UnaryHistory provenanceRead :=
    unary_cont_closed continuationUnary unaryP provenanceCont
  have terminalUnary : UnaryHistory terminalRead :=
    unary_cont_closed provenanceUnary unaryN terminalCont
  exact
    ⟨unaryO, unaryA, unaryC, unaryP, unaryN, outputUnary, continuationUnary,
      provenanceUnary, terminalUnary, outputCont, continuationCont, provenanceCont,
      terminalCont, sameTransport, provenancePkg, terminalPkg⟩

end BEDC.Derived.AuthorizedGeneratorRecursorUp
