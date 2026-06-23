import BEDC.Derived.AxiomDependencyTupleUp

namespace BEDC.Derived.AxiomDependencyTupleUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem AxiomDependencyTupleModeLedgerPriority [AskSetup] [PackageSetup]
    {mode witness supply transport route provenance localName zeroRead restrictedRead
      refusedRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    AxiomDependencyTupleCarrier mode witness supply transport route provenance localName
        bundle pkg ->
      Cont witness supply zeroRead ->
        Cont supply route restrictedRead ->
          Cont localName supply refusedRead ->
            PkgSig bundle zeroRead pkg ->
              PkgSig bundle restrictedRead pkg ->
                PkgSig bundle refusedRead pkg ->
                  (hsame mode BHist.Empty ->
                      UnaryHistory zeroRead ∧ Cont witness supply zeroRead ∧
                        PkgSig bundle zeroRead pkg) ∧
                    (hsame mode (BHist.e0 BHist.Empty) ->
                      UnaryHistory restrictedRead ∧ Cont supply route restrictedRead ∧
                        PkgSig bundle restrictedRead pkg) ∧
                    (hsame mode (BHist.e1 BHist.Empty) ->
                      UnaryHistory refusedRead ∧ Cont localName supply refusedRead ∧
                        PkgSig bundle refusedRead pkg) := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg UnaryHistory hsame Cont PkgSig
  intro carrier witnessSupplyZero supplyRouteRestricted localSupplyRefused zeroReadPkg
    restrictedReadPkg refusedReadPkg
  obtain ⟨_modeCases, _modeUnary, witnessUnary, supplyUnary, _transportUnary,
    routeUnary, localNameUnary, _transportSame, _modeWitnessRoute, _routeSupplyLocalName,
    _provenancePkg⟩ := carrier
  have zeroUnary : UnaryHistory zeroRead :=
    unary_cont_closed witnessUnary supplyUnary witnessSupplyZero
  have restrictedUnary : UnaryHistory restrictedRead :=
    unary_cont_closed supplyUnary routeUnary supplyRouteRestricted
  have refusedUnary : UnaryHistory refusedRead :=
    unary_cont_closed localNameUnary supplyUnary localSupplyRefused
  constructor
  · intro _zeroMode
    exact ⟨zeroUnary, witnessSupplyZero, zeroReadPkg⟩
  · constructor
    · intro _restrictedMode
      exact ⟨restrictedUnary, supplyRouteRestricted, restrictedReadPkg⟩
    · intro _refusedMode
      exact ⟨refusedUnary, localSupplyRefused, refusedReadPkg⟩

end BEDC.Derived.AxiomDependencyTupleUp
