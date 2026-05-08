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

theorem GaloisGroupAutomorphismActionCompositionPacket_group_law_semantic_name_certificate
    {extension group fixed action composition inverse classifier provenance ledger : BHist} :
    GaloisGroupAutomorphismActionCompositionPacket extension group fixed action composition inverse
        classifier provenance ledger ->
      SemanticNameCert
        (fun l : BHist => exists c : BHist,
          GaloisGroupAutomorphismActionCompositionPacket extension group fixed action composition
            inverse c provenance l)
        (fun l : BHist => exists c : BHist,
          GaloisGroupAutomorphismActionCompositionPacket extension group fixed action composition
            inverse c provenance l)
        (fun l : BHist => exists c : BHist,
          GaloisGroupAutomorphismActionCompositionPacket extension group fixed action composition
            inverse c provenance l)
        (fun left right : BHist =>
          (exists lc : BHist,
            GaloisGroupAutomorphismActionCompositionPacket extension group fixed action composition
              inverse lc provenance left) /\
            (exists rc : BHist,
              GaloisGroupAutomorphismActionCompositionPacket extension group fixed action composition
                inverse rc provenance right) /\
              hsame left right) := by
  intro packet
  exact {
    core := {
      carrier_inhabited := Exists.intro ledger (Exists.intro classifier packet)
      equiv_refl := by
        intro h source
        exact And.intro source (And.intro source (hsame_refl h))
      equiv_symm := by
        intro h k classified
        exact And.intro classified.right.left
          (And.intro classified.left (hsame_symm classified.right.right))
      equiv_trans := by
        intro h k r classifiedHK classifiedKR
        exact And.intro classifiedHK.left
          (And.intro classifiedKR.right.left
            (hsame_trans classifiedHK.right.right classifiedKR.right.right))
      carrier_respects_equiv := by
        intro h k classified _source
        exact classified.right.left
    }
    pattern_sound := by
      intro h source
      exact source
    ledger_sound := by
      intro h source
      exact source
  }

end BEDC.Derived.GaloisGroupUp
