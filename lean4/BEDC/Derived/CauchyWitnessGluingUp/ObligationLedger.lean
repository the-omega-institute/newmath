import BEDC.Derived.CauchyWitnessGluingUp.WitnessLedgerExactness
import BEDC.FKernel.Package.Core

namespace BEDC.Derived.CauchyWitnessGluingUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem CauchyWitnessGluingCarrier_obligation_ledger [AskSetup] [PackageSetup]
    {ledger tail synchronizer classifier stream regular dyadic realSeal edge transport route
      provenance localName witnessRead realRead publicRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CauchyWitnessGluingCarrier ledger tail synchronizer classifier stream regular dyadic realSeal
        edge transport route provenance localName ->
      Cont edge route witnessRead ->
        Cont stream dyadic regular ->
          Cont regular realSeal realRead ->
            Cont tail realRead publicRead ->
              PkgSig bundle publicRead pkg ->
                UnaryHistory witnessRead ∧ UnaryHistory realRead ∧
                  UnaryHistory publicRead ∧ Cont ledger tail edge ∧
                    Cont synchronizer classifier route ∧ Cont edge route witnessRead ∧
                      Cont stream dyadic regular ∧ Cont regular realSeal realRead ∧
                        Cont tail realRead publicRead ∧ hsame transport (append edge route) ∧
                          PkgSig bundle publicRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig hsame UnaryHistory
  intro carrier edgeRouteWitness streamDyadicRegular regularRealSealRead tailRealPublic
    publicPkg
  have witnessLedger :=
    CauchyWitnessGluingCarrier_witness_ledger_exactness carrier edgeRouteWitness
  obtain
    ⟨_ledgerUnary, tailUnary, synchronizerUnary, classifierUnary, _edgeUnary,
      witnessReadUnary, ledgerTailEdge, synchronizerClassifierRoute, edgeRouteWitnessRow,
      transportRoute⟩ := witnessLedger
  obtain
    ⟨_ledgerUnaryFromCarrier, _tailUnaryFromCarrier, _synchronizerUnaryFromCarrier,
      _classifierUnaryFromCarrier, streamUnary, _regularUnaryFromCarrier, dyadicUnary,
      realSealUnary, _edgeUnaryFromCarrier, _transportUnaryFromCarrier,
      _ledgerTailEdgeFromCarrier, _synchronizerClassifierRouteFromCarrier,
      _streamDyadicRegularFromCarrier, _regularRealSealEdgeFromCarrier,
      _transportRouteFromCarrier⟩ := carrier
  have realReadUnary : UnaryHistory realRead :=
    unary_cont_closed _regularUnaryFromCarrier realSealUnary regularRealSealRead
  have publicReadUnary : UnaryHistory publicRead :=
    unary_cont_closed tailUnary realReadUnary tailRealPublic
  exact
    ⟨witnessReadUnary, realReadUnary, publicReadUnary, ledgerTailEdge,
      synchronizerClassifierRoute, edgeRouteWitnessRow, streamDyadicRegular,
      regularRealSealRead, tailRealPublic, transportRoute, publicPkg⟩

end BEDC.Derived.CauchyWitnessGluingUp
