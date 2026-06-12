import BEDC.Derived.LawlessSequenceUp.Carrier
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.LawlessSequenceUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem LawlessSequencePrefixInductionObligation [AskSetup] [PackageSetup]
    {window boolDigits natIndex transport replay provenance localName : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} {P : BHist → Prop} :
    lawless_sequence_stream_name_handoff_carrier
        window boolDigits natIndex transport replay provenance localName bundle pkg →
      P BHist.Empty →
        (∀ h : BHist, UnaryHistory h → P h → P (BHist.e1 h)) →
          (∀ row : BHist, hsame row natIndex → P row) ∧
            (∀ z : BHist, hsame natIndex (BHist.e0 z) → False) := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg UnaryHistory hsame
  intro carrier base step
  obtain ⟨_windowUnary, _boolDigitsUnary, natIndexUnary, _transportUnary, _replayUnary,
    _provenanceUnary, _localNameUnary, _provenancePkg, _localNamePkg⟩ := carrier
  constructor
  · intro row sameRow
    have rowUnary : UnaryHistory row :=
      unary_transport_symm natIndexUnary sameRow
    exact unary_history_induction base step row rowUnary
  · intro z sameZero
    have zeroUnary : UnaryHistory (BHist.e0 z) :=
      unary_transport natIndexUnary sameZero
    exact unary_no_zero_extension zeroUnary

end BEDC.Derived.LawlessSequenceUp
