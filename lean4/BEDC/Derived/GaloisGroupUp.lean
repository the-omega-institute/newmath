import BEDC.FKernel.Cont
import BEDC.FKernel.Unary

namespace BEDC.Derived.GaloisGroupUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Unary

def GaloisGroupAutomorphismActionPacket
    (extension group fixed action composition inverse classifier provenance ledger : BHist) : Prop :=
  UnaryHistory extension ∧ UnaryHistory group ∧ UnaryHistory fixed ∧ UnaryHistory action ∧
    UnaryHistory inverse ∧ Cont extension group fixed ∧ Cont fixed action composition ∧
      Cont composition inverse classifier ∧ Cont classifier provenance ledger

theorem GaloisGroupAutomorphismActionPacket_composition_closure
    {extension group fixed action action' composition composition' inverse classifier classifier'
      provenance ledger ledger' : BHist} :
    GaloisGroupAutomorphismActionPacket extension group fixed action composition inverse classifier
        provenance ledger ->
      hsame action action' ->
        Cont fixed action' composition' ->
          Cont composition' inverse classifier' ->
            Cont classifier' provenance ledger' ->
              GaloisGroupAutomorphismActionPacket extension group fixed action' composition' inverse
                  classifier' provenance ledger' ∧
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
    {extension group fixed action composition inverse inverse' classifier classifier' provenance ledger
      ledger' : BHist} :
    GaloisGroupAutomorphismActionPacket extension group fixed action composition inverse classifier
        provenance ledger ->
      hsame inverse inverse' ->
        Cont composition inverse' classifier' ->
          Cont classifier' provenance ledger' ->
            GaloisGroupAutomorphismActionPacket extension group fixed action composition inverse'
                classifier' provenance ledger' ∧
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

end BEDC.Derived.GaloisGroupUp
