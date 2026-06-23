import BEDC.Derived.ApproximationTowerResidueUp.Carrier

namespace BEDC.Derived.ApproximationTowerResidueUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem ApproximationTowerResidue_scope_lock [AskSetup] [PackageSetup]
    {source tower classifier ledger failure recovery descent transport replay provenance
      localName recoveryRead descentRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ApproximationTowerResidueCarrier source tower classifier ledger failure recovery descent
        transport replay provenance localName bundle pkg →
      Cont recovery descent recoveryRead →
        Cont recoveryRead transport descentRead →
          PkgSig bundle recoveryRead pkg →
            UnaryHistory source ∧ UnaryHistory tower ∧ UnaryHistory classifier ∧
              UnaryHistory ledger ∧ UnaryHistory failure ∧ UnaryHistory recovery ∧
                UnaryHistory descent ∧ UnaryHistory transport ∧ UnaryHistory replay ∧
                  UnaryHistory provenance ∧ UnaryHistory localName ∧
                    UnaryHistory recoveryRead ∧ UnaryHistory descentRead ∧
                      Cont source tower classifier ∧ Cont classifier ledger failure ∧
                        Cont failure recovery descent ∧ Cont descent transport replay ∧
                          Cont replay provenance localName ∧ PkgSig bundle localName pkg ∧
                            PkgSig bundle recoveryRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont UnaryHistory
  intro carrier recoveryRoute descentRoute recoveryPkg
  obtain ⟨sourceUnary, towerUnary, classifierUnary, ledgerUnary, failureUnary,
    recoveryUnary, descentUnary, transportUnary, replayUnary, provenanceUnary,
    localNameUnary, sourceTowerClassifier, classifierLedgerFailure,
    failureRecoveryDescent, descentTransportReplay, replayProvenanceLocalName,
    localPkg⟩ := carrier
  have recoveryReadUnary : UnaryHistory recoveryRead :=
    unary_cont_closed recoveryUnary descentUnary recoveryRoute
  have descentReadUnary : UnaryHistory descentRead :=
    unary_cont_closed recoveryReadUnary transportUnary descentRoute
  exact
    ⟨sourceUnary, towerUnary, classifierUnary, ledgerUnary, failureUnary, recoveryUnary,
      descentUnary, transportUnary, replayUnary, provenanceUnary, localNameUnary,
      recoveryReadUnary, descentReadUnary, sourceTowerClassifier, classifierLedgerFailure,
      failureRecoveryDescent, descentTransportReplay, replayProvenanceLocalName, localPkg,
      recoveryPkg⟩

end BEDC.Derived.ApproximationTowerResidueUp
