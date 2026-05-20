import BEDC.Derived.RealityConstrainedSynthesisSealUp.TasteGate
import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.RealityConstrainedSynthesisSealUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem RealityConstrainedSynthesisSeal_independence_boundary
    (x : RealityConstrainedSynthesisSealUp) :
    Exists fun audit : BHist =>
      Exists fun fit : BHist =>
        Exists fun objectivity : BHist =>
          Exists fun observation : BHist =>
            Exists fun explanation : BHist =>
              Exists fun tower : BHist =>
                Exists fun ledger : BHist =>
                  Exists fun failure : BHist =>
                    Exists fun transport : BHist =>
                      Exists fun replay : BHist =>
                        Exists fun provenance : BHist =>
                          Exists fun name : BHist =>
                            Exists fun auditFit : BHist =>
                              Exists fun fitObjectivity : BHist =>
                                Exists fun objectivityObservation : BHist =>
                                  Exists fun towerLedger : BHist =>
                                    Exists fun failureReplay : BHist =>
                                      Exists fun finalName : BHist =>
                                        x =
                                            RealityConstrainedSynthesisSealUp.mk audit fit
                                              objectivity observation explanation tower ledger
                                              failure transport replay provenance name ∧
                                          realityConstrainedSynthesisSealFields x =
                                            [audit, fit, objectivity, observation, explanation,
                                              tower, ledger, failure, transport, replay,
                                              provenance, name] ∧
                                            Cont audit fit auditFit ∧
                                              Cont fit objectivity fitObjectivity ∧
                                                Cont objectivity observation
                                                    objectivityObservation ∧
                                                  Cont tower ledger towerLedger ∧
                                                    Cont failure replay failureReplay ∧
                                                      Cont provenance name finalName ∧
                                                        hsame finalName
                                                          (append provenance name) := by
  -- BEDC touchpoint anchor: BHist Cont hsame
  cases x with
  | mk audit fit objectivity observation explanation tower ledger failure transport replay
      provenance name =>
      exact
        Exists.intro audit
          (Exists.intro fit
            (Exists.intro objectivity
              (Exists.intro observation
                (Exists.intro explanation
                  (Exists.intro tower
                    (Exists.intro ledger
                      (Exists.intro failure
                        (Exists.intro transport
                          (Exists.intro replay
                            (Exists.intro provenance
                              (Exists.intro name
                                (Exists.intro (append audit fit)
                                  (Exists.intro (append fit objectivity)
                                    (Exists.intro (append objectivity observation)
                                      (Exists.intro (append tower ledger)
                                        (Exists.intro (append failure replay)
                                          (Exists.intro (append provenance name)
                                            ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl,
                                              rfl⟩)))))))))))))))))

theorem RealityConstrainedSynthesisSealUp_independence_boundary [AskSetup] [PackageSetup]
    {audit fit objectivity observation explanation tower ledger failure transport replay
      provenance name auditFit fitObjectivity objectivityObservation explanationTower towerLedger
      failureReplay finalName : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    UnaryHistory audit →
      UnaryHistory fit →
        UnaryHistory objectivity →
          UnaryHistory observation →
            UnaryHistory explanation →
              UnaryHistory tower →
                UnaryHistory ledger →
                  UnaryHistory failure →
                    UnaryHistory replay →
                      UnaryHistory provenance →
                        UnaryHistory name →
                          Cont audit fit auditFit →
                            Cont fit objectivity fitObjectivity →
                              Cont objectivity observation objectivityObservation →
                                Cont explanation tower explanationTower →
                                  Cont tower ledger towerLedger →
                                    Cont failure replay failureReplay →
                                      Cont provenance name finalName →
                                        PkgSig bundle finalName pkg →
                                          let packet :=
                                            RealityConstrainedSynthesisSealUp.mk audit fit
                                              objectivity observation explanation tower ledger
                                              failure transport replay provenance name
                                          realityConstrainedSynthesisSealFields packet =
                                              [audit, fit, objectivity, observation,
                                                explanation, tower, ledger, failure,
                                                transport, replay, provenance, name] ∧
                                            UnaryHistory auditFit ∧
                                              UnaryHistory fitObjectivity ∧
                                                UnaryHistory objectivityObservation ∧
                                                  UnaryHistory explanationTower ∧
                                                    UnaryHistory towerLedger ∧
                                                      UnaryHistory failureReplay ∧
                                                        UnaryHistory finalName ∧
                                                          List.Mem audit
                                                            (realityConstrainedSynthesisSealFields
                                                              packet) ∧
                                                            List.Mem fit
                                                              (realityConstrainedSynthesisSealFields
                                                                packet) ∧
                                                              List.Mem objectivity
                                                                (realityConstrainedSynthesisSealFields
                                                                  packet) ∧
                                                                List.Mem observation
                                                                  (realityConstrainedSynthesisSealFields
                                                                    packet) ∧
                                                                  List.Mem explanation
                                                                    (realityConstrainedSynthesisSealFields
                                                                      packet) ∧
                                                                    PkgSig bundle finalName pkg := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle Pkg PkgSig UnaryHistory
  intro auditUnary fitUnary objectivityUnary observationUnary explanationUnary towerUnary
    ledgerUnary failureUnary replayUnary provenanceUnary nameUnary auditFitCont
    fitObjectivityCont objectivityObservationCont explanationTowerCont towerLedgerCont
    failureReplayCont finalNameCont finalNamePkg
  let packet :=
    RealityConstrainedSynthesisSealUp.mk audit fit objectivity observation explanation tower ledger
      failure transport replay provenance name
  have auditFitUnary : UnaryHistory auditFit :=
    unary_cont_closed auditUnary fitUnary auditFitCont
  have fitObjectivityUnary : UnaryHistory fitObjectivity :=
    unary_cont_closed fitUnary objectivityUnary fitObjectivityCont
  have objectivityObservationUnary : UnaryHistory objectivityObservation :=
    unary_cont_closed objectivityUnary observationUnary objectivityObservationCont
  have explanationTowerUnary : UnaryHistory explanationTower :=
    unary_cont_closed explanationUnary towerUnary explanationTowerCont
  have towerLedgerUnary : UnaryHistory towerLedger :=
    unary_cont_closed towerUnary ledgerUnary towerLedgerCont
  have failureReplayUnary : UnaryHistory failureReplay :=
    unary_cont_closed failureUnary replayUnary failureReplayCont
  have finalNameUnary : UnaryHistory finalName :=
    unary_cont_closed provenanceUnary nameUnary finalNameCont
  exact
    ⟨rfl, auditFitUnary, fitObjectivityUnary, objectivityObservationUnary,
      explanationTowerUnary, towerLedgerUnary, failureReplayUnary, finalNameUnary, by
        exact List.Mem.head [fit, objectivity, observation, explanation, tower, ledger,
          failure, transport, replay, provenance, name], by
        exact
          List.Mem.tail audit
            (List.Mem.head [objectivity, observation, explanation, tower, ledger, failure,
              transport, replay, provenance, name]), by
        exact
          List.Mem.tail audit
            (List.Mem.tail fit
              (List.Mem.head [observation, explanation, tower, ledger, failure, transport,
                replay, provenance, name])), by
        exact
          List.Mem.tail audit
            (List.Mem.tail fit
              (List.Mem.tail objectivity
                (List.Mem.head [explanation, tower, ledger, failure, transport, replay,
                  provenance, name]))), by
        exact
          List.Mem.tail audit
            (List.Mem.tail fit
              (List.Mem.tail objectivity
                (List.Mem.tail observation
                  (List.Mem.head [tower, ledger, failure, transport, replay, provenance,
                    name])))), finalNamePkg⟩

end BEDC.Derived.RealityConstrainedSynthesisSealUp
