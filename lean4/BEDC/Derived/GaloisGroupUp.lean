import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.Package
import BEDC.FKernel.Unary
import BEDC.FKernel.Unary.History

namespace BEDC.Derived.GaloisGroupUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
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

theorem GaloisGroupAutomorphismActionPacket_inverse_closure
    {extension group fixed action composition inverse classifier provenance ledger inverseAction
      inverseClassifier inverseLedger : BHist} :
    GaloisGroupAutomorphismActionCompositionPacket extension group fixed action composition
        inverse classifier provenance ledger ->
      Cont fixed inverse inverseAction ->
        Cont inverseAction action inverseClassifier ->
          Cont inverseClassifier provenance inverseLedger ->
            GaloisGroupAutomorphismActionCompositionPacket extension group fixed inverse
                inverseAction action inverseClassifier provenance inverseLedger ∧
              hsame inverseAction (append fixed inverse) ∧
                hsame inverseClassifier (append (append fixed inverse) action) ∧
                  hsame inverseLedger
                    (append (append (append fixed inverse) action) provenance) := by
  intro packet inverseActionCont inverseClassifierCont inverseLedgerCont
  have inverseActionUnary : UnaryHistory inverseAction :=
    unary_cont_closed packet.right.right.left packet.right.right.right.right.left
      inverseActionCont
  have inverseClassifierUnary : UnaryHistory inverseClassifier :=
    unary_cont_closed inverseActionUnary packet.right.right.right.left inverseClassifierCont
  have inverseClassifierSame : hsame inverseClassifier (append (append fixed inverse) action) := by
    exact hsame_trans inverseClassifierCont
      (congrArg (fun row : BHist => append row action) inverseActionCont)
  have inverseLedgerSame :
      hsame inverseLedger (append (append (append fixed inverse) action) provenance) := by
    exact hsame_trans inverseLedgerCont
      (congrArg (fun row : BHist => append row provenance) inverseClassifierSame)
  exact And.intro
    (And.intro packet.left
      (And.intro packet.right.left
        (And.intro packet.right.right.left
          (And.intro packet.right.right.right.right.left
            (And.intro packet.right.right.right.left
              (And.intro packet.right.right.right.right.right.left
                (And.intro inverseActionCont
                  (And.intro inverseClassifierCont inverseLedgerCont))))))))
    (And.intro inverseActionCont
      (And.intro inverseClassifierSame inverseLedgerSame))

end BEDC.Derived.GaloisGroupUp
