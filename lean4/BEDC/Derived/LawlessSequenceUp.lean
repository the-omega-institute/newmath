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

end BEDC.Derived.LawlessSequenceUp
