import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.FastCauchyUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
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

theorem FastCauchyPacket_semantic_name_certificate [AskSetup] [PackageSetup]
    {stream modulus endpoint latePair transport window provenance nameRow : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    FastCauchyPacket stream modulus endpoint latePair transport window provenance nameRow
        bundle pkg ->
      SemanticNameCert
        (fun row : BHist =>
          FastCauchyPacket stream modulus endpoint latePair transport window provenance nameRow
            bundle pkg ∧ hsame row provenance)
        (fun row : BHist =>
          FastCauchyPacket stream modulus endpoint latePair transport window provenance nameRow
            bundle pkg ∧ hsame row provenance)
        (fun row : BHist =>
          FastCauchyPacket stream modulus endpoint latePair transport window provenance nameRow
            bundle pkg ∧ hsame row provenance)
        hsame := by
  intro packet
  exact {
    core := {
      carrier_inhabited :=
        Exists.intro provenance (And.intro packet (hsame_refl provenance))
      equiv_refl := by
        intro row _source
        exact hsame_refl row
      equiv_symm := by
        intro row row' sameRows
        exact hsame_symm sameRows
      equiv_trans := by
        intro row row' row'' sameLeft sameRight
        exact hsame_trans sameLeft sameRight
      carrier_respects_equiv := by
        intro row row' sameRows source
        exact And.intro source.left (hsame_trans (hsame_symm sameRows) source.right)
    }
    pattern_sound := by
      intro _row source
      exact source
    ledger_sound := by
      intro _row source
      exact source
  }

end BEDC.Derived.FastCauchyUp
