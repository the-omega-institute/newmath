import BEDC.Derived.FareySequenceUp.TasteGate
import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.FareySequenceUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem FareySequenceStreamWindowAdjacencyScope [AskSetup] [PackageSetup]
    {B A M L T S D Q W R G E H C P N windowRead adjacencyRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    FareySequenceCarrier B A M L T S D Q W R G E H C P N bundle pkg ->
      Cont B W windowRead ->
        Cont windowRead A adjacencyRead ->
          PkgSig bundle P pkg ->
            UnaryHistory windowRead ∧ UnaryHistory adjacencyRead ∧ Cont B W windowRead ∧
              Cont windowRead A adjacencyRead ∧ PkgSig bundle P pkg := by
  -- BEDC touchpoint anchor: FareySequenceCarrier BHist Cont ProbeBundle PkgSig UnaryHistory
  intro carrier windowRoute adjacencyRoute provenancePkg
  obtain ⟨bUnary, aUnary, _mUnary, _lUnary, _tUnary, _sUnary, _dUnary, _qUnary,
    wUnary, _rUnary, _gUnary, _eUnary, _hUnary, _cUnary, _pUnary, _nUnary,
    _aEmpty, _sEmpty, _mEmpty, _gEmpty, _eEmpty, _carrierPkg⟩ := carrier
  have windowUnary : UnaryHistory windowRead :=
    unary_cont_closed bUnary wUnary windowRoute
  have adjacencyUnary : UnaryHistory adjacencyRead :=
    unary_cont_closed windowUnary aUnary adjacencyRoute
  exact ⟨windowUnary, adjacencyUnary, windowRoute, adjacencyRoute, provenancePkg⟩

end BEDC.Derived.FareySequenceUp
