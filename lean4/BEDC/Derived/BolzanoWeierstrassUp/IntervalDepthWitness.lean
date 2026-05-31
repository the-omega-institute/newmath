import BEDC.Derived.BolzanoWeierstrassUp.FiniteSubsequenceObligations

namespace BEDC.Derived.BolzanoWeierstrassUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem BolzanoWeierstrassCarrier_interval_depth_witness [AskSetup] [PackageSetup]
    {S K R Q E H C P N depthCell retainedCell boundedWindow nextLedger
      depthWitness : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    BolzanoWeierstrassCarrier S K R Q E H C P N bundle pkg ->
      Cont S K depthCell ->
        Cont depthCell K retainedCell ->
          Cont retainedCell S boundedWindow ->
            Cont boundedWindow R nextLedger ->
              Cont nextLedger Q depthWitness ->
                PkgSig bundle depthWitness pkg ->
                  UnaryHistory S ∧ UnaryHistory K ∧ UnaryHistory R ∧ UnaryHistory Q ∧
                    UnaryHistory depthCell ∧ UnaryHistory retainedCell ∧
                      UnaryHistory boundedWindow ∧ UnaryHistory nextLedger ∧
                        UnaryHistory depthWitness ∧ Cont S K depthCell ∧
                          Cont depthCell K retainedCell ∧
                            Cont retainedCell S boundedWindow ∧
                              Cont boundedWindow R nextLedger ∧
                                Cont nextLedger Q depthWitness ∧ PkgSig bundle P pkg ∧
                                  PkgSig bundle depthWitness pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont UnaryHistory PkgSig
  intro carrier depthRoute retainedRoute boundedRoute ledgerRoute witnessRoute witnessPkg
  obtain ⟨SUnary, KUnary, RUnary, QUnary, _EUnary, _HUnary, _CUnary, _PUnary,
    _NUnary, _sourceIntervalRoute, _readbackSealRoute, _transportReplayRoute,
    carrierPkg⟩ := carrier
  have depthCellUnary : UnaryHistory depthCell :=
    unary_cont_closed SUnary KUnary depthRoute
  have retainedCellUnary : UnaryHistory retainedCell :=
    unary_cont_closed depthCellUnary KUnary retainedRoute
  have boundedWindowUnary : UnaryHistory boundedWindow :=
    unary_cont_closed retainedCellUnary SUnary boundedRoute
  have nextLedgerUnary : UnaryHistory nextLedger :=
    unary_cont_closed boundedWindowUnary RUnary ledgerRoute
  have depthWitnessUnary : UnaryHistory depthWitness :=
    unary_cont_closed nextLedgerUnary QUnary witnessRoute
  exact
    ⟨SUnary, KUnary, RUnary, QUnary, depthCellUnary, retainedCellUnary,
      boundedWindowUnary, nextLedgerUnary, depthWitnessUnary, depthRoute, retainedRoute,
      boundedRoute, ledgerRoute, witnessRoute, carrierPkg, witnessPkg⟩

end BEDC.Derived.BolzanoWeierstrassUp
