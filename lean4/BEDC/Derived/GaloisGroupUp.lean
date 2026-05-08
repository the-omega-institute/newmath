import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary
import BEDC.FKernel.Unary.History

namespace BEDC.Derived.GaloisGroupUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def GaloisGroupAutomorphismActionPacket [AskSetup] [PackageSetup]
    (galoisExt group fixedBase action composition inverse classifier provenance ledger
      endpoint : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  UnaryHistory galoisExt ∧ UnaryHistory group ∧ UnaryHistory fixedBase ∧
    UnaryHistory action ∧ UnaryHistory composition ∧ UnaryHistory inverse ∧
      Cont galoisExt group provenance ∧ Cont fixedBase action classifier ∧
        Cont composition inverse ledger ∧ Cont provenance ledger endpoint ∧
          PkgSig bundle endpoint pkg

theorem GaloisGroupAutomorphismActionPacket_fixed_base_carrier_obligation
    [AskSetup] [PackageSetup]
    {galoisExt group fixedBase action composition inverse classifier provenance ledger
      endpoint : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    GaloisGroupAutomorphismActionPacket galoisExt group fixedBase action composition inverse
        classifier provenance ledger endpoint bundle pkg ->
      UnaryHistory provenance ∧ UnaryHistory classifier ∧ UnaryHistory ledger ∧
        UnaryHistory endpoint ∧ hsame provenance (append galoisExt group) ∧
          hsame classifier (append fixedBase action) ∧
            hsame ledger (append composition inverse) ∧
              hsame endpoint (append provenance ledger) ∧ PkgSig bundle endpoint pkg := by
  intro packet
  have provenanceUnary : UnaryHistory provenance :=
    unary_cont_closed packet.left packet.right.left
      packet.right.right.right.right.right.right.left
  have classifierUnary : UnaryHistory classifier :=
    unary_cont_closed packet.right.right.left packet.right.right.right.left
      packet.right.right.right.right.right.right.right.left
  have ledgerUnary : UnaryHistory ledger :=
    unary_cont_closed packet.right.right.right.right.left
      packet.right.right.right.right.right.left
      packet.right.right.right.right.right.right.right.right.left
  have endpointUnary : UnaryHistory endpoint :=
    unary_cont_closed provenanceUnary ledgerUnary
      packet.right.right.right.right.right.right.right.right.right.left
  exact And.intro provenanceUnary
    (And.intro classifierUnary
      (And.intro ledgerUnary
        (And.intro endpointUnary
          (And.intro packet.right.right.right.right.right.right.left
            (And.intro packet.right.right.right.right.right.right.right.left
              (And.intro packet.right.right.right.right.right.right.right.right.left
                (And.intro packet.right.right.right.right.right.right.right.right.right.left
                  packet.right.right.right.right.right.right.right.right.right.right)))))))

def GaloisGroupAutomorphismActionCompositionPacket
    (extension group fixed action composition inverse classifier provenance ledger : BHist) : Prop :=
  UnaryHistory extension ∧ UnaryHistory group ∧ UnaryHistory fixed ∧ UnaryHistory action ∧
    UnaryHistory inverse ∧ Cont extension group fixed ∧ Cont fixed action composition ∧
      Cont composition inverse classifier ∧ Cont classifier provenance ledger

theorem GaloisGroupAutomorphismActionPacket_composition_closure
    {extension group fixed action action' composition composition' inverse classifier classifier'
      provenance ledger ledger' : BHist} :
    GaloisGroupAutomorphismActionCompositionPacket extension group fixed action composition inverse
        classifier provenance ledger ->
      hsame action action' ->
        Cont fixed action' composition' ->
          Cont composition' inverse classifier' ->
            Cont classifier' provenance ledger' ->
              GaloisGroupAutomorphismActionCompositionPacket extension group fixed action' composition'
                  inverse classifier' provenance ledger' ∧
                hsame composition composition' ∧ hsame classifier classifier' ∧
                  hsame ledger ledger' := by
  intro packet sameAction actionRow classifierRow ledgerRow
  have actionUnary : UnaryHistory action' :=
    unary_transport packet.right.right.right.left sameAction
  have sameComposition : hsame composition composition' :=
    cont_respects_hsame (hsame_refl fixed) sameAction packet.right.right.right.right.right.right.left
      actionRow
  have sameClassifier : hsame classifier classifier' :=
    cont_respects_hsame sameComposition (hsame_refl inverse)
      packet.right.right.right.right.right.right.right.left classifierRow
  have sameLedger : hsame ledger ledger' :=
    cont_respects_hsame sameClassifier (hsame_refl provenance)
      packet.right.right.right.right.right.right.right.right ledgerRow
  exact And.intro
    (And.intro packet.left
      (And.intro packet.right.left
        (And.intro packet.right.right.left
          (And.intro actionUnary
            (And.intro packet.right.right.right.right.left
              (And.intro packet.right.right.right.right.right.left
                (And.intro actionRow (And.intro classifierRow ledgerRow))))))))
    (And.intro sameComposition (And.intro sameClassifier sameLedger))

theorem GaloisGroupAutomorphismActionPacket_identity_action_row [AskSetup] [PackageSetup]
    {galois group base action composition inverse classifier provenance ledger endpoint
      identityAction identityEndpoint : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    GaloisGroupAutomorphismActionPacket galois group base action composition inverse
        classifier provenance ledger endpoint bundle pkg ->
      Cont galois BHist.Empty identityAction ->
        Cont identityAction group identityEndpoint ->
          UnaryHistory identityAction ∧ UnaryHistory identityEndpoint ∧
            hsame identityAction galois ∧ hsame identityEndpoint (append identityAction group) ∧
              PkgSig bundle endpoint pkg := by
  intro packet identityRow endpointRow
  have identityUnary : UnaryHistory identityAction :=
    unary_cont_closed packet.left unary_empty identityRow
  have endpointUnary : UnaryHistory identityEndpoint :=
    unary_cont_closed identityUnary packet.right.left endpointRow
  have sameIdentity : hsame identityAction galois :=
    cont_deterministic identityRow (cont_right_unit galois)
  exact And.intro identityUnary
    (And.intro endpointUnary
      (And.intro sameIdentity
        (And.intro endpointRow
          packet.right.right.right.right.right.right.right.right.right.right)))

theorem GaloisGroupAutomorphismActionPacket_inverse_cancellation_rows
    {extension group fixed action composition inverse classifier provenance ledger inverse'
      classifier' ledger' : BHist} :
    GaloisGroupAutomorphismActionCompositionPacket extension group fixed action composition inverse
        classifier provenance ledger ->
      hsame inverse inverse' ->
        Cont composition inverse' classifier' ->
          Cont classifier' provenance ledger' ->
            GaloisGroupAutomorphismActionCompositionPacket extension group fixed action composition
                inverse' classifier' provenance ledger' ∧
              hsame classifier classifier' ∧ hsame ledger ledger' := by
  intro packet sameInverse classifierRow ledgerRow
  have inverseUnary : UnaryHistory inverse' :=
    unary_transport packet.right.right.right.right.left sameInverse
  have sameClassifier : hsame classifier classifier' :=
    cont_respects_hsame (hsame_refl composition) sameInverse
      packet.right.right.right.right.right.right.right.left classifierRow
  have sameLedger : hsame ledger ledger' :=
    cont_respects_hsame sameClassifier (hsame_refl provenance)
      packet.right.right.right.right.right.right.right.right ledgerRow
  exact And.intro
    (And.intro packet.left
      (And.intro packet.right.left
        (And.intro packet.right.right.left
          (And.intro packet.right.right.right.left
            (And.intro inverseUnary
              (And.intro packet.right.right.right.right.right.left
                (And.intro packet.right.right.right.right.right.right.left
                  (And.intro classifierRow ledgerRow))))))))
    (And.intro sameClassifier sameLedger)

theorem GaloisGroupAutomorphismActionPacket_semantic_name_certificate [AskSetup]
    [PackageSetup]
    {galois group base action composition inverse classifier provenance ledger endpoint : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    GaloisGroupAutomorphismActionPacket galois group base action composition inverse
        classifier provenance ledger endpoint bundle pkg ->
      SemanticNameCert
        (fun target : BHist =>
          exists carriedClassifier carriedProvenance carriedLedger : BHist,
            GaloisGroupAutomorphismActionPacket galois group base action composition inverse
              carriedClassifier carriedProvenance carriedLedger target bundle pkg)
        (fun target : BHist =>
          exists carriedClassifier carriedProvenance carriedLedger : BHist,
            GaloisGroupAutomorphismActionPacket galois group base action composition inverse
              carriedClassifier carriedProvenance carriedLedger target bundle pkg)
        (fun target : BHist =>
          exists carriedClassifier carriedProvenance carriedLedger : BHist,
            GaloisGroupAutomorphismActionPacket galois group base action composition inverse
              carriedClassifier carriedProvenance carriedLedger target bundle pkg)
        (fun left right : BHist =>
          (exists leftClassifier leftProvenance leftLedger : BHist,
            GaloisGroupAutomorphismActionPacket galois group base action composition inverse
              leftClassifier leftProvenance leftLedger left bundle pkg) /\
            (exists rightClassifier rightProvenance rightLedger : BHist,
              GaloisGroupAutomorphismActionPacket galois group base action composition inverse
                rightClassifier rightProvenance rightLedger right bundle pkg) /\
              hsame left right) := by
  intro packet
  exact {
    core := {
      carrier_inhabited :=
        Exists.intro endpoint
          (Exists.intro classifier (Exists.intro provenance (Exists.intro ledger packet)))
      equiv_refl := by
        intro target targetPacket
        exact And.intro targetPacket (And.intro targetPacket (hsame_refl target))
      equiv_symm := by
        intro left right classified
        exact And.intro classified.right.left
          (And.intro classified.left (hsame_symm classified.right.right))
      equiv_trans := by
        intro left middle right leftMiddle middleRight
        exact And.intro leftMiddle.left
          (And.intro middleRight.right.left
            (hsame_trans leftMiddle.right.right middleRight.right.right))
      carrier_respects_equiv := by
        intro left right classified _leftPacket
        exact classified.right.left
    }
    pattern_sound := by
      intro _target source
      exact source
    ledger_sound := by
      intro _target source
      exact source
  }

end BEDC.Derived.GaloisGroupUp
