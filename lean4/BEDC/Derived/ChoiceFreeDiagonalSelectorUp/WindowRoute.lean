import BEDC.Derived.ChoiceFreeDiagonalSelectorUp.TasteGate
import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.ChoiceFreeDiagonalSelectorUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def ChoiceFreeDiagonalSelectorCarrier [AskSetup] [PackageSetup]
    (epsilon window stream readback realSeal transport replay provenance localName : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  UnaryHistory epsilon ∧ UnaryHistory window ∧ UnaryHistory stream ∧
    UnaryHistory readback ∧ UnaryHistory realSeal ∧ UnaryHistory transport ∧
      UnaryHistory replay ∧ UnaryHistory provenance ∧ UnaryHistory localName ∧
        Cont epsilon window transport ∧ Cont stream readback replay ∧
          PkgSig bundle provenance pkg

theorem ChoiceFreeDiagonalSelectorCarrier_window_route [AskSetup] [PackageSetup]
    {epsilon window stream readback realSeal transport replay provenance localName windowRead
      witnessRead sealRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ChoiceFreeDiagonalSelectorCarrier epsilon window stream readback realSeal transport replay
        provenance localName bundle pkg →
      Cont epsilon window windowRead →
        Cont windowRead stream witnessRead →
          Cont witnessRead readback sealRead →
            UnaryHistory windowRead ∧ UnaryHistory witnessRead ∧ UnaryHistory sealRead ∧
              Cont epsilon window windowRead ∧ Cont windowRead stream witnessRead ∧
                Cont witnessRead readback sealRead ∧ PkgSig bundle provenance pkg := by
  -- BEDC touchpoint anchor: ChoiceFreeDiagonalSelectorCarrier BHist Cont ProbeBundle PkgSig UnaryHistory
  intro carrier epsilonWindow windowStream witnessReadback
  obtain ⟨epsilonUnary, windowUnary, streamUnary, readbackUnary, _realSealUnary,
    _transportUnary, _replayUnary, _provenanceUnary, _localNameUnary, _storedWindowRoute,
    _storedReplayRoute, provenancePkg⟩ := carrier
  have windowReadUnary : UnaryHistory windowRead :=
    unary_cont_closed epsilonUnary windowUnary epsilonWindow
  have witnessReadUnary : UnaryHistory witnessRead :=
    unary_cont_closed windowReadUnary streamUnary windowStream
  have sealReadUnary : UnaryHistory sealRead :=
    unary_cont_closed witnessReadUnary readbackUnary witnessReadback
  exact
    ⟨windowReadUnary, witnessReadUnary, sealReadUnary, epsilonWindow, windowStream,
      witnessReadback, provenancePkg⟩

end BEDC.Derived.ChoiceFreeDiagonalSelectorUp
