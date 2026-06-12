import BEDC.Derived.LawlessSequenceUp

namespace BEDC.Derived.LawlessSequenceUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem LawlessSequencePrefixWindowDeterminacy [AskSetup] [PackageSetup]
    {W B I H C P N W' B' I' H' C' P' N' read read' digit digit' named
      named' : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    lawless_sequence_stream_name_handoff_carrier W B I H C P N bundle pkg ->
      lawless_sequence_stream_name_handoff_carrier W' B' I' H' C' P' N' bundle pkg ->
        hsame I I' ->
          hsame W W' ->
            hsame B B' ->
              hsame N N' ->
                Cont I W read ->
                  Cont read B digit ->
                    Cont digit N named ->
                      Cont I' W' read' ->
                        Cont read' B' digit' ->
                          Cont digit' N' named' ->
                            hsame read read' ∧ hsame digit digit' ∧ hsame named named' ∧
                              UnaryHistory read ∧ UnaryHistory read' ∧
                                UnaryHistory digit ∧ UnaryHistory digit' ∧
                                  UnaryHistory named ∧ UnaryHistory named' := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg UnaryHistory Cont PkgSig hsame
  intro carrier carrier' sameIndex sameWindow sameBool sameName indexWindow windowDigit
    digitName indexWindow' windowDigit' digitName'
  obtain ⟨windowUnary, boolUnary, indexUnary, _transportUnary, _replayUnary,
    _provenanceUnary, nameUnary, _provenancePkg, _namePkg⟩ := carrier
  obtain ⟨windowUnary', boolUnary', indexUnary', _transportUnary', _replayUnary',
    _provenanceUnary', nameUnary', _provenancePkg', _namePkg'⟩ := carrier'
  have sameRead : hsame read read' :=
    cont_respects_hsame sameIndex sameWindow indexWindow indexWindow'
  have sameDigit : hsame digit digit' :=
    cont_respects_hsame sameRead sameBool windowDigit windowDigit'
  have sameNamed : hsame named named' :=
    cont_respects_hsame sameDigit sameName digitName digitName'
  have readUnary : UnaryHistory read :=
    unary_cont_closed indexUnary windowUnary indexWindow
  have readUnary' : UnaryHistory read' :=
    unary_cont_closed indexUnary' windowUnary' indexWindow'
  have digitUnary : UnaryHistory digit :=
    unary_cont_closed readUnary boolUnary windowDigit
  have digitUnary' : UnaryHistory digit' :=
    unary_cont_closed readUnary' boolUnary' windowDigit'
  have namedUnary : UnaryHistory named :=
    unary_cont_closed digitUnary nameUnary digitName
  have namedUnary' : UnaryHistory named' :=
    unary_cont_closed digitUnary' nameUnary' digitName'
  exact
    ⟨sameRead, sameDigit, sameNamed, readUnary, readUnary', digitUnary, digitUnary',
      namedUnary, namedUnary'⟩

end BEDC.Derived.LawlessSequenceUp
