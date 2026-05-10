import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.Package
import BEDC.FKernel.Sig
import BEDC.FKernel.Unary

namespace BEDC.Derived.BeliefUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Sig
open BEDC.FKernel.Unary

theorem BeliefObservationUpdatePacket_transport_obligation [AskSetup] [PackageSetup]
    {prior observation update probability posterior ledger prior' observation' update' probability'
      posterior' ledger' : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    UnaryHistory prior -> UnaryHistory observation -> UnaryHistory probability ->
      Cont prior observation update -> Cont update probability posterior ->
        Cont prior' observation' update' -> Cont update' probability' posterior' ->
          hsame prior prior' -> hsame observation observation' -> hsame probability probability' ->
            hsame ledger ledger' -> SigRel bundle ledger posterior ->
              PkgSig bundle posterior pkg ->
                UnaryHistory update' ∧ UnaryHistory posterior' ∧ hsame update update' ∧
                  hsame posterior posterior' ∧ SigRel bundle ledger posterior ∧
                    PkgSig bundle posterior pkg := by
  intro priorUnary observationUnary probabilityUnary updateRow posteriorRow updateRow'
  intro posteriorRow' samePrior sameObservation sameProbability _sameLedger sigRel pkgSig
  have priorUnary' : UnaryHistory prior' := unary_transport priorUnary samePrior
  have observationUnary' : UnaryHistory observation' :=
    unary_transport observationUnary sameObservation
  have probabilityUnary' : UnaryHistory probability' :=
    unary_transport probabilityUnary sameProbability
  have updateUnary' : UnaryHistory update' :=
    unary_cont_closed priorUnary' observationUnary' updateRow'
  have posteriorUnary' : UnaryHistory posterior' :=
    unary_cont_closed updateUnary' probabilityUnary' posteriorRow'
  have sameUpdate : hsame update update' :=
    cont_respects_hsame samePrior sameObservation updateRow updateRow'
  have samePosterior : hsame posterior posterior' :=
    cont_respects_hsame sameUpdate sameProbability posteriorRow posteriorRow'
  exact ⟨updateUnary', posteriorUnary', sameUpdate, samePosterior, sigRel, pkgSig⟩

end BEDC.Derived.BeliefUp
