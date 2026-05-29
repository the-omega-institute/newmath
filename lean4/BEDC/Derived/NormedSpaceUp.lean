import BEDC.Derived.NormedSpaceUp.TasteGate
import BEDC.FKernel.Ask
import BEDC.FKernel.Cont
import BEDC.FKernel.Package.Core
import BEDC.FKernel.Unary.History

namespace BEDC.Derived.NormedSpaceUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def NormedSpaceCarrier (V R N Z T S M C P K : BHist) : Prop :=
  -- BEDC touchpoint anchor: BHist Cont UnaryHistory
  UnaryHistory V ∧ UnaryHistory R ∧ UnaryHistory N ∧ UnaryHistory Z ∧
    UnaryHistory T ∧ UnaryHistory S ∧ UnaryHistory M ∧ UnaryHistory C ∧
      UnaryHistory P ∧ UnaryHistory K

theorem NormedSpaceCarrier_zero_exactness [AskSetup] [PackageSetup]
    {V R N Z T S M C P K zeroNorm zeroRoute : BHist} :
    NormedSpaceCarrier V R N Z T S M C P K ->
      Cont Z N zeroNorm ->
        Cont V zeroNorm zeroRoute ->
          UnaryHistory zeroNorm /\ UnaryHistory zeroRoute := by
  -- BEDC touchpoint anchor: BHist Cont UnaryHistory AskSetup PackageSetup
  intro carrier zeroNormCont zeroRouteCont
  obtain ⟨vUnary, _rUnary, nUnary, zUnary, _tUnary, _sUnary, _mUnary, _cUnary,
    _pUnary, _kUnary⟩ := carrier
  have zeroNormUnary : UnaryHistory zeroNorm :=
    unary_cont_closed zUnary nUnary zeroNormCont
  have zeroRouteUnary : UnaryHistory zeroRoute :=
    unary_cont_closed vUnary zeroNormUnary zeroRouteCont
  exact ⟨zeroNormUnary, zeroRouteUnary⟩

end BEDC.Derived.NormedSpaceUp
