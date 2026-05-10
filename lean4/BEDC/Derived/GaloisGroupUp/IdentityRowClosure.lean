import BEDC.Derived.GaloisGroupUp

namespace BEDC.Derived.GaloisGroupUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem GaloisGroupAutomorphismActionPacket_identity_row_closure [AskSetup] [PackageSetup]
    {galoisExt group fixedBase action composition inverse classifier provenance ledger endpoint
      identity classifier' ledger' : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    GaloisGroupAutomorphismActionPacket galoisExt group fixedBase action composition inverse
        classifier provenance ledger endpoint bundle pkg ->
      Cont action BHist.Empty identity ->
        Cont fixedBase identity classifier' ->
          Cont composition inverse ledger' ->
            GaloisGroupAutomorphismActionPacket galoisExt group fixedBase identity composition inverse
                classifier' provenance ledger' endpoint bundle pkg ∧
              hsame identity action ∧ hsame classifier classifier' ∧ hsame ledger ledger' := by
  intro packet identityCont classifierCont' ledgerCont'
  have sameIdentity : hsame identity action :=
    cont_right_unit_result identityCont
  have sameClassifier : hsame classifier classifier' :=
    cont_respects_hsame (hsame_refl fixedBase) (hsame_symm sameIdentity)
      packet.right.right.right.right.right.right.right.left classifierCont'
  have sameLedger : hsame ledger ledger' :=
    cont_respects_hsame (hsame_refl composition) (hsame_refl inverse)
      packet.right.right.right.right.right.right.right.right.left ledgerCont'
  have identityUnary : UnaryHistory identity :=
    unary_transport packet.right.right.right.left (hsame_symm sameIdentity)
  have endpointCont' : Cont provenance ledger' endpoint := by
    cases sameLedger
    exact packet.right.right.right.right.right.right.right.right.right.left
  exact And.intro
    (And.intro packet.left
      (And.intro packet.right.left
        (And.intro packet.right.right.left
          (And.intro identityUnary
            (And.intro packet.right.right.right.right.left
              (And.intro packet.right.right.right.right.right.left
                (And.intro packet.right.right.right.right.right.right.left
                  (And.intro classifierCont'
                    (And.intro ledgerCont'
                      (And.intro endpointCont'
                        packet.right.right.right.right.right.right.right.right.right.right))))))))))
    (And.intro sameIdentity (And.intro sameClassifier sameLedger))

end BEDC.Derived.GaloisGroupUp
