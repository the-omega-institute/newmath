import BEDC.Derived.LawlessSequenceUp.TasteGate
import BEDC.FKernel.Package.Core
import BEDC.FKernel.Unary.History

namespace BEDC.Derived.LawlessSequenceUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def lawless_sequence_stream_name_handoff_carrier [AskSetup] [PackageSetup]
    (window boolDigits natIndex transport replay provenance localName : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg UnaryHistory PkgSig
  UnaryHistory window ∧
    UnaryHistory boolDigits ∧
      UnaryHistory natIndex ∧
        UnaryHistory transport ∧
          UnaryHistory replay ∧
            UnaryHistory provenance ∧
              UnaryHistory localName ∧
                PkgSig bundle provenance pkg ∧ PkgSig bundle localName pkg

theorem LawlessSequenceStreamNameHandoff [AskSetup] [PackageSetup]
    {window boolDigits natIndex transport replay provenance localName streamRead namedRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    lawless_sequence_stream_name_handoff_carrier
        window boolDigits natIndex transport replay provenance localName bundle pkg →
      Cont natIndex window streamRead →
        Cont streamRead boolDigits namedRead →
          PkgSig bundle namedRead pkg →
            UnaryHistory window ∧
              UnaryHistory boolDigits ∧
                UnaryHistory natIndex ∧
                  UnaryHistory streamRead ∧
                    UnaryHistory namedRead ∧
                      Cont natIndex window streamRead ∧
                        Cont streamRead boolDigits namedRead ∧
                          PkgSig bundle provenance pkg ∧ PkgSig bundle namedRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg UnaryHistory Cont PkgSig
  intro carrier indexWindow windowDigit namedPkg
  obtain ⟨windowUnary, boolUnary, indexUnary, _transportUnary, _replayUnary,
    _provenanceUnary, _localNameUnary, provenancePkg, _localNamePkg⟩ := carrier
  have streamUnary : UnaryHistory streamRead :=
    unary_cont_closed indexUnary windowUnary indexWindow
  have namedUnary : UnaryHistory namedRead :=
    unary_cont_closed streamUnary boolUnary windowDigit
  exact
    ⟨windowUnary, boolUnary, indexUnary, streamUnary, namedUnary, indexWindow,
      windowDigit, provenancePkg, namedPkg⟩

theorem LawlessSequenceFinitePrefixInduction [AskSetup] [PackageSetup]
    {window boolDigits natIndex transport replay provenance localName prefixRead digitRead
      replayRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    lawless_sequence_stream_name_handoff_carrier
        window boolDigits natIndex transport replay provenance localName bundle pkg →
      Cont natIndex window prefixRead →
        Cont prefixRead boolDigits digitRead →
          Cont digitRead replay replayRead →
            PkgSig bundle replayRead pkg →
              UnaryHistory natIndex ∧
                UnaryHistory window ∧
                  UnaryHistory boolDigits ∧
                    UnaryHistory prefixRead ∧
                      UnaryHistory digitRead ∧
                        UnaryHistory replayRead ∧
                          Cont natIndex window prefixRead ∧
                            Cont prefixRead boolDigits digitRead ∧
                              Cont digitRead replay replayRead ∧
                                PkgSig bundle provenance pkg ∧
                                  PkgSig bundle replayRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg UnaryHistory Cont PkgSig
  intro carrier indexWindow prefixDigit digitReplay replayPkg
  obtain ⟨windowUnary, boolUnary, indexUnary, _transportUnary, replayUnary,
    _provenanceUnary, _localNameUnary, provenancePkg, _localNamePkg⟩ := carrier
  have prefixUnary : UnaryHistory prefixRead :=
    unary_cont_closed indexUnary windowUnary indexWindow
  have digitUnary : UnaryHistory digitRead :=
    unary_cont_closed prefixUnary boolUnary prefixDigit
  have replayReadUnary : UnaryHistory replayRead :=
    unary_cont_closed digitUnary replayUnary digitReplay
  exact
    ⟨indexUnary, windowUnary, boolUnary, prefixUnary, digitUnary, replayReadUnary,
      indexWindow, prefixDigit, digitReplay, provenancePkg, replayPkg⟩

end BEDC.Derived.LawlessSequenceUp
