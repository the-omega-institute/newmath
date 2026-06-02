import BEDC.Derived.FareySequenceUp.TasteGate
import BEDC.FKernel.Package.Core
import BEDC.FKernel.Unary.History

namespace BEDC.Derived.FareySequenceUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem FareySequenceCarrier_adjacency_obligation [AskSetup] [PackageSetup]
    {B A M L T S D Q W R G E H C P N adjacencyRead sternRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    FareySequenceCarrier B A M L T S D Q W R G E H C P N bundle pkg ->
      Cont B A adjacencyRead ->
        Cont A S sternRead ->
          PkgSig bundle P pkg ->
            UnaryHistory B ∧ UnaryHistory A ∧ UnaryHistory S ∧
              UnaryHistory adjacencyRead ∧ UnaryHistory sternRead ∧
                Cont B A adjacencyRead ∧ Cont A S sternRead ∧
                  hsame adjacencyRead (append B A) ∧ hsame sternRead (append A S) ∧
                    PkgSig bundle P pkg := by
  -- BEDC touchpoint anchor: FareySequenceCarrier BHist ProbeBundle Pkg Cont hsame UnaryHistory
  intro carrier adjacencyRoute sternRoute pkgSig
  obtain ⟨bUnary, aUnary, _mUnary, _lUnary, _tUnary, sUnary, _dUnary, _qUnary,
    _wUnary, _rUnary, _gUnary, _eUnary, _hUnary, _cUnary, _pUnary, _nUnary,
    _aEmpty, _sEmpty, _mEmpty, _gEmpty, _eEmpty, _storedPkgSig⟩ := carrier
  have adjacencyUnary : UnaryHistory adjacencyRead :=
    unary_cont_closed bUnary aUnary adjacencyRoute
  have sternUnary : UnaryHistory sternRead :=
    unary_cont_closed aUnary sUnary sternRoute
  have adjacencyExact : hsame adjacencyRead (append B A) := by
    cases adjacencyRoute
    exact hsame_refl _
  have sternExact : hsame sternRead (append A S) := by
    cases sternRoute
    exact hsame_refl _
  exact
    ⟨bUnary, aUnary, sUnary, adjacencyUnary, sternUnary, adjacencyRoute, sternRoute,
      adjacencyExact, sternExact, pkgSig⟩

end BEDC.Derived.FareySequenceUp
