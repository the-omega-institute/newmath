import BEDC.Derived.FareySequenceUp.TasteGate

namespace BEDC.Derived.FareySequenceUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem FareySequenceCarrier_neighbor_determinacy [AskSetup] [PackageSetup]
    {B A M L T S D Q W R G E H C P N adjacencyRead mediantRead routeRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    FareySequenceCarrier B A M L T S D Q W R G E H C P N bundle pkg ->
      Cont A S adjacencyRead ->
        Cont adjacencyRead M mediantRead ->
          Cont mediantRead S routeRead ->
            hsame adjacencyRead BHist.Empty ∧ hsame mediantRead BHist.Empty ∧
              hsame routeRead BHist.Empty ∧ PkgSig bundle P pkg := by
  -- BEDC touchpoint anchor: FareySequenceCarrier BHist Cont ProbeBundle PkgSig hsame
  intro carrier adjacencyRoute mediantRoute routeRoute
  obtain ⟨_bUnary, _aUnary, _mUnary, _lUnary, _tUnary, _sUnary, _dUnary, _qUnary,
    _wUnary, _rUnary, _gUnary, _eUnary, _hUnary, _cUnary, _pUnary, _nUnary,
      aEmpty, sEmpty, mEmpty, _gEmpty, _eEmpty, provenancePkg⟩ := carrier
  cases aEmpty
  cases sEmpty
  cases mEmpty
  have adjacencyEmpty : hsame adjacencyRead BHist.Empty :=
    cont_left_unit_result adjacencyRoute
  have mediantEmpty : hsame mediantRead BHist.Empty := by
    cases adjacencyEmpty
    exact cont_left_unit_result mediantRoute
  have routeEmpty : hsame routeRead BHist.Empty := by
    cases mediantEmpty
    exact cont_left_unit_result routeRoute
  exact ⟨adjacencyEmpty, mediantEmpty, routeEmpty, provenancePkg⟩

end BEDC.Derived.FareySequenceUp
