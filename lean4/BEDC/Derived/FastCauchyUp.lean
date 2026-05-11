import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.FastCauchyUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def FastCauchyPacket [AskSetup] [PackageSetup]
    (stream modulus endpoint latePair transport window provenance nameRow : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  UnaryHistory stream ∧ UnaryHistory modulus ∧ UnaryHistory endpoint ∧
    UnaryHistory latePair ∧ UnaryHistory transport ∧ UnaryHistory window ∧
      UnaryHistory provenance ∧ UnaryHistory nameRow ∧ Cont stream modulus endpoint ∧
        Cont endpoint latePair window ∧ Cont window transport provenance ∧
          PkgSig bundle provenance pkg

theorem FastCauchyPacket_modulus_transport [AskSetup] [PackageSetup]
    {stream modulus endpoint latePair transport window provenance nameRow stream' modulus'
      endpoint' latePair' transport' window' provenance' nameRow' : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    FastCauchyPacket stream modulus endpoint latePair transport window provenance nameRow
        bundle pkg ->
      hsame stream stream' ->
        hsame modulus modulus' ->
          hsame latePair latePair' ->
            hsame transport transport' ->
              hsame nameRow nameRow' ->
                Cont stream' modulus' endpoint' ->
                  Cont endpoint' latePair' window' ->
                    Cont window' transport' provenance' ->
                      PkgSig bundle provenance' pkg ->
                        FastCauchyPacket stream' modulus' endpoint' latePair' transport'
                            window' provenance' nameRow' bundle pkg ∧
                          hsame endpoint endpoint' ∧ hsame window window' ∧
                            hsame provenance provenance' := by
  intro packet sameStream sameModulus sameLatePair sameTransport sameNameRow
    targetEndpoint targetWindow targetProvenance targetPkg
  have streamUnary : UnaryHistory stream :=
    packet.left
  have modulusUnary : UnaryHistory modulus :=
    packet.right.left
  have latePairUnary : UnaryHistory latePair :=
    packet.right.right.right.left
  have transportUnary : UnaryHistory transport :=
    packet.right.right.right.right.left
  have nameRowUnary : UnaryHistory nameRow :=
    packet.right.right.right.right.right.right.right.left
  have sourceEndpoint : Cont stream modulus endpoint :=
    packet.right.right.right.right.right.right.right.right.left
  have sourceWindow : Cont endpoint latePair window :=
    packet.right.right.right.right.right.right.right.right.right.left
  have sourceProvenance : Cont window transport provenance :=
    packet.right.right.right.right.right.right.right.right.right.right.left
  have streamUnary' : UnaryHistory stream' :=
    unary_transport streamUnary sameStream
  have modulusUnary' : UnaryHistory modulus' :=
    unary_transport modulusUnary sameModulus
  have endpointUnary' : UnaryHistory endpoint' :=
    unary_cont_closed streamUnary' modulusUnary' targetEndpoint
  have latePairUnary' : UnaryHistory latePair' :=
    unary_transport latePairUnary sameLatePair
  have transportUnary' : UnaryHistory transport' :=
    unary_transport transportUnary sameTransport
  have windowUnary' : UnaryHistory window' :=
    unary_cont_closed endpointUnary' latePairUnary' targetWindow
  have provenanceUnary' : UnaryHistory provenance' :=
    unary_cont_closed windowUnary' transportUnary' targetProvenance
  have nameRowUnary' : UnaryHistory nameRow' :=
    unary_transport nameRowUnary sameNameRow
  have sameEndpoint : hsame endpoint endpoint' :=
    cont_respects_hsame sameStream sameModulus sourceEndpoint targetEndpoint
  have sameWindow : hsame window window' :=
    cont_respects_hsame sameEndpoint sameLatePair sourceWindow targetWindow
  have sameProvenance : hsame provenance provenance' :=
    cont_respects_hsame sameWindow sameTransport sourceProvenance targetProvenance
  exact
    ⟨⟨streamUnary', modulusUnary', endpointUnary', latePairUnary', transportUnary',
        windowUnary', provenanceUnary', nameRowUnary', targetEndpoint, targetWindow,
        targetProvenance, targetPkg⟩,
      sameEndpoint, sameWindow, sameProvenance⟩

def FastCauchyFiniteCarrier [AskSetup] [PackageSetup]
    (stream modulus endpoint radius comparison transportWindow regWindow sealBoundary certRow : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  UnaryHistory stream ∧ UnaryHistory modulus ∧ UnaryHistory endpoint ∧ UnaryHistory radius ∧
    UnaryHistory comparison ∧ UnaryHistory transportWindow ∧ UnaryHistory regWindow ∧
      UnaryHistory sealBoundary ∧ UnaryHistory certRow ∧ Cont stream modulus transportWindow ∧
        Cont endpoint radius comparison ∧ Cont comparison transportWindow regWindow ∧
          Cont regWindow sealBoundary certRow ∧ PkgSig bundle regWindow pkg

def FastCauchyRegSeqRatWindow [AskSetup] [PackageSetup]
    (stream modulus endpoint radius comparison transportWindow regWindow handoff : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  UnaryHistory stream ∧ UnaryHistory modulus ∧ UnaryHistory endpoint ∧ UnaryHistory radius ∧
    UnaryHistory comparison ∧ UnaryHistory transportWindow ∧ UnaryHistory regWindow ∧
      UnaryHistory handoff ∧ Cont regWindow endpoint handoff ∧ PkgSig bundle regWindow pkg

theorem FastCauchyFiniteCarrier_regseqrat_handoff [AskSetup] [PackageSetup]
    {stream modulus endpoint radius comparison transportWindow regWindow sealBoundary certRow
      handoff : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    FastCauchyFiniteCarrier stream modulus endpoint radius comparison transportWindow regWindow
        sealBoundary certRow bundle pkg ->
      Cont regWindow endpoint handoff ->
        FastCauchyRegSeqRatWindow stream modulus endpoint radius comparison transportWindow regWindow
            handoff bundle pkg ∧
          UnaryHistory handoff ∧ hsame handoff (append regWindow endpoint) := by
  intro carrier handoffRow
  obtain ⟨streamUnary, modulusUnary, endpointUnary, radiusUnary, comparisonUnary,
    transportWindowUnary, regWindowUnary, _sealBoundaryUnary, _certRowUnary, _transportRow,
    _comparisonRow, _regWindowRow, _certRow, pkgRow⟩ := carrier
  have handoffUnary : UnaryHistory handoff :=
    unary_cont_closed regWindowUnary endpointUnary handoffRow
  exact
    ⟨⟨streamUnary, modulusUnary, endpointUnary, radiusUnary, comparisonUnary,
        transportWindowUnary, regWindowUnary, handoffUnary, handoffRow, pkgRow⟩,
      handoffUnary,
      handoffRow⟩

end BEDC.Derived.FastCauchyUp
