import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.Package
import BEDC.FKernel.Unary.History

namespace BEDC.Derived.DyadicMidpointUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def DyadicMidpointCarrier [AskSetup] [PackageSetup]
    (left right scale midpoint branch window transport route provenance name : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  UnaryHistory left ∧ UnaryHistory right ∧ UnaryHistory scale ∧ UnaryHistory midpoint ∧
    UnaryHistory branch ∧ UnaryHistory window ∧ UnaryHistory transport ∧
      UnaryHistory route ∧ UnaryHistory provenance ∧ UnaryHistory name ∧
        Cont left right scale ∧ Cont scale midpoint window ∧ Cont branch window route ∧
          PkgSig bundle provenance pkg ∧ PkgSig bundle name pkg

theorem DyadicMidpointCarrier_readback_closure [AskSetup] [PackageSetup]
    {left right scale midpoint branch window transport route provenance name : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    DyadicMidpointCarrier left right scale midpoint branch window transport route provenance
        name bundle pkg ->
      UnaryHistory window ∧ UnaryHistory route ∧ Cont scale midpoint window ∧
        Cont branch window route ∧ PkgSig bundle name pkg := by
  intro carrier
  obtain ⟨_leftUnary, _rightUnary, scaleUnary, midpointUnary, branchUnary,
    _windowUnary, _transportUnary, _routeUnary, _provenanceUnary, _nameUnary,
    _endpointRoute, midpointRoute, branchRoute, _provenanceSig, nameSig⟩ := carrier
  have windowClosed : UnaryHistory window :=
    unary_cont_closed scaleUnary midpointUnary midpointRoute
  have routeClosed : UnaryHistory route :=
    unary_cont_closed branchUnary windowClosed branchRoute
  exact ⟨windowClosed, routeClosed, midpointRoute, branchRoute, nameSig⟩

end BEDC.Derived.DyadicMidpointUp
