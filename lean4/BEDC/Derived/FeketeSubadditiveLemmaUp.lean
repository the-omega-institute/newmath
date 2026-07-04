import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.FeketeSubadditiveLemmaUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem FeketeSubadditiveLemmaCarrier_tail_infimum_route [AskSetup] [PackageSetup]
    {S A Q T I R E H C P N avgRead tailRead infRead regularRead realRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    UnaryHistory S ∧ UnaryHistory A ∧ UnaryHistory Q ∧ UnaryHistory T ∧
      UnaryHistory I ∧ UnaryHistory R ∧ UnaryHistory E ∧ UnaryHistory H ∧
        UnaryHistory C ∧ UnaryHistory P ∧ UnaryHistory N ∧
          Cont S A avgRead ∧ Cont avgRead Q tailRead ∧ Cont tailRead T infRead ∧
            Cont infRead I regularRead ∧ Cont regularRead R realRead ∧
              Cont realRead E C ∧ PkgSig bundle P pkg ∧ PkgSig bundle N pkg →
      UnaryHistory avgRead ∧ UnaryHistory tailRead ∧ UnaryHistory infRead ∧
        UnaryHistory regularRead ∧ UnaryHistory realRead ∧ Cont S A avgRead ∧
          Cont avgRead Q tailRead ∧ Cont tailRead T infRead ∧
            Cont infRead I regularRead ∧ Cont regularRead R realRead ∧
              Cont realRead E C ∧ PkgSig bundle P pkg ∧ PkgSig bundle N pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig UnaryHistory
  intro carrier
  obtain ⟨sUnary, aUnary, qUnary, tUnary, iUnary, rUnary, eUnary, _hUnary,
    _cUnary, _pUnary, _nUnary, avgRoute, tailRoute, infRoute, regularRoute, realRoute,
      endpointRoute, pPkg, nPkg⟩ := carrier
  have avgUnary : UnaryHistory avgRead :=
    unary_cont_closed sUnary aUnary avgRoute
  have tailUnary : UnaryHistory tailRead :=
    unary_cont_closed avgUnary qUnary tailRoute
  have infUnary : UnaryHistory infRead :=
    unary_cont_closed tailUnary tUnary infRoute
  have regularUnary : UnaryHistory regularRead :=
    unary_cont_closed infUnary iUnary regularRoute
  have realUnary : UnaryHistory realRead :=
    unary_cont_closed regularUnary rUnary realRoute
  exact
    ⟨avgUnary, tailUnary, infUnary, regularUnary, realUnary, avgRoute, tailRoute, infRoute,
      regularRoute, realRoute, endpointRoute, pPkg, nPkg⟩

end BEDC.Derived.FeketeSubadditiveLemmaUp
