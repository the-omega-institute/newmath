import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.DiagonalLimitUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def DiagonalLimitCarrier [AskSetup] [PackageSetup]
    (family modulus stream dyadic completion «seal» route provenance : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  UnaryHistory family ∧ UnaryHistory modulus ∧ UnaryHistory stream ∧
    UnaryHistory dyadic ∧ UnaryHistory completion ∧ UnaryHistory «seal» ∧
      UnaryHistory route ∧ UnaryHistory provenance ∧ Cont family modulus stream ∧
        Cont stream dyadic completion ∧ Cont completion «seal» route ∧
          Cont route provenance (append route provenance) ∧ PkgSig bundle provenance pkg

theorem DiagonalLimitCarrier_completion_seal_factorization [AskSetup] [PackageSetup]
    {family modulus stream dyadic completion «seal» route provenance consumer : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    DiagonalLimitCarrier family modulus stream dyadic completion «seal» route provenance
        bundle pkg ->
      Cont completion «seal» route ->
        Cont route provenance consumer ->
          UnaryHistory consumer ∧ hsame route (append completion «seal») ∧
            hsame consumer (append route provenance) ∧ PkgSig bundle provenance pkg := by
  intro carrier completionSealRow routeProvenanceConsumer
  obtain ⟨_familyUnary, _modulusUnary, _streamUnary, _dyadicUnary, completionUnary,
    sealUnary, routeUnary, provenanceUnary, _familyModulusRow, _streamDyadicRow,
    _storedCompletionSealRow, _storedRouteProvenanceRow, provenancePkg⟩ := carrier
  have routeSame : hsame route (append completion «seal») := completionSealRow
  have consumerSame : hsame consumer (append route provenance) := routeProvenanceConsumer
  have consumerUnary : UnaryHistory consumer :=
    unary_cont_closed routeUnary provenanceUnary routeProvenanceConsumer
  have _routeUnaryFromRows : UnaryHistory route :=
    unary_cont_closed completionUnary sealUnary completionSealRow
  exact ⟨consumerUnary, routeSame, consumerSame, provenancePkg⟩

end BEDC.Derived.DiagonalLimitUp
