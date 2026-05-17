import BEDC.Derived.UniformCauchyCriterionUp

namespace BEDC.Derived.UniformCauchyCriterionUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem UniformCauchyCriterionPacket_phase_real_exit_consumer_exhaustion
    [AskSetup] [PackageSetup]
    {index windows modulus tolerance tail sealRow transports routes provenance name streamRead
      regseqRead selectorRead terminalRead returnRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    UniformCauchyCriterionPacket index windows modulus tolerance tail sealRow transports routes
        provenance name bundle pkg ->
      Cont index windows streamRead ->
        Cont streamRead tail regseqRead ->
          Cont tail sealRow selectorRead ->
            Cont selectorRead sealRow terminalRead ->
              Cont terminalRead name returnRead ->
                PkgSig bundle streamRead pkg ->
                  PkgSig bundle regseqRead pkg ->
                    PkgSig bundle selectorRead pkg ->
                      PkgSig bundle terminalRead pkg ->
                        PkgSig bundle returnRead pkg ->
                          UnaryHistory streamRead ∧ UnaryHistory regseqRead ∧
                            UnaryHistory selectorRead ∧ UnaryHistory terminalRead ∧
                              UnaryHistory returnRead ∧ Cont index windows streamRead ∧
                                Cont streamRead tail regseqRead ∧
                                  Cont tail sealRow selectorRead ∧
                                    Cont selectorRead sealRow terminalRead ∧
                                      Cont terminalRead name returnRead ∧
                                        PkgSig bundle name pkg ∧
                                          PkgSig bundle returnRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont UnaryHistory
  intro packet indexWindowsStream streamTailRegseq tailSealSelector selectorSealTerminal
    terminalNameReturn _streamPkg _regseqPkg _selectorPkg _terminalPkg returnPkg
  obtain ⟨indexUnary, windowsUnary, _modulusUnary, _toleranceUnary, tailUnary, sealRowUnary,
    _transportsUnary, _routesUnary, _provenanceUnary, nameUnary, _indexWindowsModulus,
    _modulusToleranceTail, _tailSealRowTransports, _transportsRoutesProvenance, namePkg⟩ :=
    packet
  have streamUnary : UnaryHistory streamRead :=
    unary_cont_closed indexUnary windowsUnary indexWindowsStream
  have regseqUnary : UnaryHistory regseqRead :=
    unary_cont_closed streamUnary tailUnary streamTailRegseq
  have selectorUnary : UnaryHistory selectorRead :=
    unary_cont_closed tailUnary sealRowUnary tailSealSelector
  have terminalUnary : UnaryHistory terminalRead :=
    unary_cont_closed selectorUnary sealRowUnary selectorSealTerminal
  have returnUnary : UnaryHistory returnRead :=
    unary_cont_closed terminalUnary nameUnary terminalNameReturn
  exact
    ⟨streamUnary, regseqUnary, selectorUnary, terminalUnary, returnUnary, indexWindowsStream,
      streamTailRegseq, tailSealSelector, selectorSealTerminal, terminalNameReturn, namePkg,
      returnPkg⟩

end BEDC.Derived.UniformCauchyCriterionUp
