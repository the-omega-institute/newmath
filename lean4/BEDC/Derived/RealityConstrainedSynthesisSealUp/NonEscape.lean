import BEDC.Derived.RealityConstrainedSynthesisSealUp.NameCertObligations
import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.RealityConstrainedSynthesisSealUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem RealityConstrainedSynthesisSealUp_nonescape [AskSetup] [PackageSetup]
    {audit fit objectivity observation explanation tower ledger failure transport replay
      provenance name auditFit fitObjectivity objectivityObservation towerLedger failureReplay
      finalName consumerRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    UnaryHistory audit →
      UnaryHistory fit →
        UnaryHistory objectivity →
          UnaryHistory observation →
            UnaryHistory explanation →
              UnaryHistory tower →
                UnaryHistory ledger →
                  UnaryHistory failure →
                    UnaryHistory transport →
                      UnaryHistory replay →
                        UnaryHistory provenance →
                          UnaryHistory name →
                            Cont audit fit auditFit →
                              Cont fit objectivity fitObjectivity →
                                Cont objectivity observation objectivityObservation →
                                  Cont tower ledger towerLedger →
                                    Cont failure replay failureReplay →
                                      Cont provenance name finalName →
                                        Cont finalName replay consumerRead →
                                          PkgSig bundle finalName pkg →
                                            SemanticNameCert
                                                (fun row : BHist =>
                                                  hsame row consumerRead ∧ UnaryHistory row)
                                                (fun row : BHist =>
                                                  hsame row auditFit ∨
                                                    hsame row fitObjectivity ∨
                                                      hsame row objectivityObservation ∨
                                                        hsame row towerLedger ∨
                                                          hsame row failureReplay ∨
                                                            hsame row finalName ∨
                                                              hsame row consumerRead)
                                                (fun row : BHist =>
                                                  PkgSig bundle finalName pkg ∧
                                                    hsame row consumerRead ∧
                                                      Cont finalName replay consumerRead)
                                                hsame ∧
                                              UnaryHistory auditFit ∧
                                                UnaryHistory fitObjectivity ∧
                                                  UnaryHistory objectivityObservation ∧
                                                    UnaryHistory towerLedger ∧
                                                      UnaryHistory failureReplay ∧
                                                        UnaryHistory finalName ∧
                                                          UnaryHistory consumerRead := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle Pkg SemanticNameCert hsame UnaryHistory
  intro auditUnary fitUnary objectivityUnary observationUnary _explanationUnary towerUnary
    ledgerUnary failureUnary _transportUnary replayUnary provenanceUnary nameUnary auditFitCont
    fitObjectivityCont objectivityObservationCont towerLedgerCont failureReplayCont finalNameCont
    consumerReadCont finalNamePkg
  have auditFitUnary : UnaryHistory auditFit :=
    unary_cont_closed auditUnary fitUnary auditFitCont
  have fitObjectivityUnary : UnaryHistory fitObjectivity :=
    unary_cont_closed fitUnary objectivityUnary fitObjectivityCont
  have objectivityObservationUnary : UnaryHistory objectivityObservation :=
    unary_cont_closed objectivityUnary observationUnary objectivityObservationCont
  have towerLedgerUnary : UnaryHistory towerLedger :=
    unary_cont_closed towerUnary ledgerUnary towerLedgerCont
  have failureReplayUnary : UnaryHistory failureReplay :=
    unary_cont_closed failureUnary replayUnary failureReplayCont
  have finalNameUnary : UnaryHistory finalName :=
    unary_cont_closed provenanceUnary nameUnary finalNameCont
  have consumerReadUnary : UnaryHistory consumerRead :=
    unary_cont_closed finalNameUnary replayUnary consumerReadCont
  have sourceConsumer :
      (fun row : BHist => hsame row consumerRead ∧ UnaryHistory row) consumerRead := by
    exact ⟨hsame_refl consumerRead, consumerReadUnary⟩
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row consumerRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row auditFit ∨
              hsame row fitObjectivity ∨
                hsame row objectivityObservation ∨
                  hsame row towerLedger ∨
                    hsame row failureReplay ∨ hsame row finalName ∨ hsame row consumerRead)
          (fun row : BHist =>
            PkgSig bundle finalName pkg ∧ hsame row consumerRead ∧
              Cont finalName replay consumerRead)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro consumerRead sourceConsumer
      equiv_refl := by
        intro row _source
        exact hsame_refl row
      equiv_symm := by
        intro _row _other same
        exact hsame_symm same
      equiv_trans := by
        intro _row _middle _other sameLeft sameRight
        exact hsame_trans sameLeft sameRight
      carrier_respects_equiv := by
        intro _row _other same source
        exact
          ⟨hsame_trans (hsame_symm same) source.left,
            unary_transport source.right same⟩
    }
    pattern_sound := by
      intro _row source
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr source.left)))))
    ledger_sound := by
      intro _row source
      exact ⟨finalNamePkg, source.left, consumerReadCont⟩
  }
  exact
    ⟨cert, auditFitUnary, fitObjectivityUnary, objectivityObservationUnary, towerLedgerUnary,
      failureReplayUnary, finalNameUnary, consumerReadUnary⟩

end BEDC.Derived.RealityConstrainedSynthesisSealUp
