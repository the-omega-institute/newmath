import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.AtiyahSingerUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def AtiyahSingerIndexPairingCarrierPacket [AskSetup] [PackageSetup]
    (m operator symbol spectral analytic chern characteristic topological equality
      provenance endpoint : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  UnaryHistory m ∧ UnaryHistory operator ∧ UnaryHistory symbol ∧ UnaryHistory spectral ∧
    UnaryHistory analytic ∧ UnaryHistory chern ∧ UnaryHistory characteristic ∧
      Cont spectral analytic equality ∧ Cont chern characteristic topological ∧
        Cont equality symbol provenance ∧ Cont provenance topological endpoint ∧
          PkgSig bundle endpoint pkg

theorem AtiyahSingerIndexPairingCarrierPacket_carrier_surface [AskSetup] [PackageSetup]
    {m operator symbol spectral analytic chern characteristic topological equality
      provenance endpoint : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    AtiyahSingerIndexPairingCarrierPacket m operator symbol spectral analytic chern
        characteristic topological equality provenance endpoint bundle pkg ->
      UnaryHistory equality ∧ UnaryHistory topological ∧ UnaryHistory provenance ∧
        UnaryHistory endpoint ∧ hsame equality (append spectral analytic) ∧
          hsame topological (append chern characteristic) ∧
            hsame provenance (append equality symbol) ∧ PkgSig bundle endpoint pkg := by
  intro packet
  have symbolUnary : UnaryHistory symbol :=
    packet.right.right.left
  have spectralUnary : UnaryHistory spectral :=
    packet.right.right.right.left
  have analyticUnary : UnaryHistory analytic :=
    packet.right.right.right.right.left
  have chernUnary : UnaryHistory chern :=
    packet.right.right.right.right.right.left
  have characteristicUnary : UnaryHistory characteristic :=
    packet.right.right.right.right.right.right.left
  have equalityCont : Cont spectral analytic equality :=
    packet.right.right.right.right.right.right.right.left
  have topologicalCont : Cont chern characteristic topological :=
    packet.right.right.right.right.right.right.right.right.left
  have provenanceCont : Cont equality symbol provenance :=
    packet.right.right.right.right.right.right.right.right.right.left
  have endpointCont : Cont provenance topological endpoint :=
    packet.right.right.right.right.right.right.right.right.right.right.left
  have pkgSig : PkgSig bundle endpoint pkg :=
    packet.right.right.right.right.right.right.right.right.right.right.right
  have equalityUnary : UnaryHistory equality :=
    unary_cont_closed spectralUnary analyticUnary equalityCont
  have topologicalUnary : UnaryHistory topological :=
    unary_cont_closed chernUnary characteristicUnary topologicalCont
  have provenanceUnary : UnaryHistory provenance :=
    unary_cont_closed equalityUnary symbolUnary provenanceCont
  have endpointUnary : UnaryHistory endpoint :=
    unary_cont_closed provenanceUnary topologicalUnary endpointCont
  exact And.intro equalityUnary
    (And.intro topologicalUnary
      (And.intro provenanceUnary
        (And.intro endpointUnary
          (And.intro equalityCont
            (And.intro topologicalCont
              (And.intro provenanceCont pkgSig))))))

theorem AtiyahSingerIndexPairingCarrierPacket_provenance_exactness [AskSetup] [PackageSetup]
    {m operator symbol spectral analytic chern characteristic topological equality
      provenance endpoint : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    AtiyahSingerIndexPairingCarrierPacket m operator symbol spectral analytic chern
        characteristic topological equality provenance endpoint bundle pkg ->
      UnaryHistory m ∧ UnaryHistory symbol ∧ UnaryHistory equality ∧ UnaryHistory topological ∧
        UnaryHistory provenance ∧ UnaryHistory endpoint ∧ hsame equality (append spectral analytic) ∧
          hsame topological (append chern characteristic) ∧
            hsame provenance (append equality symbol) ∧
              hsame endpoint (append provenance topological) ∧ PkgSig bundle endpoint pkg := by
  intro packet
  have mUnary : UnaryHistory m :=
    packet.left
  have symbolUnary : UnaryHistory symbol :=
    packet.right.right.left
  have spectralUnary : UnaryHistory spectral :=
    packet.right.right.right.left
  have analyticUnary : UnaryHistory analytic :=
    packet.right.right.right.right.left
  have chernUnary : UnaryHistory chern :=
    packet.right.right.right.right.right.left
  have characteristicUnary : UnaryHistory characteristic :=
    packet.right.right.right.right.right.right.left
  have equalityCont : Cont spectral analytic equality :=
    packet.right.right.right.right.right.right.right.left
  have topologicalCont : Cont chern characteristic topological :=
    packet.right.right.right.right.right.right.right.right.left
  have provenanceCont : Cont equality symbol provenance :=
    packet.right.right.right.right.right.right.right.right.right.left
  have endpointCont : Cont provenance topological endpoint :=
    packet.right.right.right.right.right.right.right.right.right.right.left
  have pkgSig : PkgSig bundle endpoint pkg :=
    packet.right.right.right.right.right.right.right.right.right.right.right
  have equalityUnary : UnaryHistory equality :=
    unary_cont_closed spectralUnary analyticUnary equalityCont
  have topologicalUnary : UnaryHistory topological :=
    unary_cont_closed chernUnary characteristicUnary topologicalCont
  have provenanceUnary : UnaryHistory provenance :=
    unary_cont_closed equalityUnary symbolUnary provenanceCont
  have endpointUnary : UnaryHistory endpoint :=
    unary_cont_closed provenanceUnary topologicalUnary endpointCont
  exact And.intro mUnary
    (And.intro symbolUnary
      (And.intro equalityUnary
        (And.intro topologicalUnary
          (And.intro provenanceUnary
            (And.intro endpointUnary
              (And.intro equalityCont
                (And.intro topologicalCont
                  (And.intro provenanceCont
                  (And.intro endpointCont pkgSig)))))))))

theorem AtiyahSingerIndexPairingCarrierPacket_classifier_coverage [AskSetup] [PackageSetup]
    {m operator symbol spectral analytic chern characteristic topological equality
      provenance endpoint : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    AtiyahSingerIndexPairingCarrierPacket m operator symbol spectral analytic chern
        characteristic topological equality provenance endpoint bundle pkg ->
      UnaryHistory m ∧ UnaryHistory symbol ∧ UnaryHistory equality ∧ UnaryHistory topological ∧
        UnaryHistory provenance ∧ UnaryHistory endpoint ∧ hsame equality (append spectral analytic) ∧
          hsame topological (append chern characteristic) ∧
            hsame provenance (append equality symbol) ∧
              hsame endpoint (append provenance topological) ∧ PkgSig bundle endpoint pkg ∧
                Cont spectral analytic equality ∧ Cont chern characteristic topological := by
  intro packet
  have mUnary : UnaryHistory m :=
    packet.left
  have symbolUnary : UnaryHistory symbol :=
    packet.right.right.left
  have spectralUnary : UnaryHistory spectral :=
    packet.right.right.right.left
  have analyticUnary : UnaryHistory analytic :=
    packet.right.right.right.right.left
  have chernUnary : UnaryHistory chern :=
    packet.right.right.right.right.right.left
  have characteristicUnary : UnaryHistory characteristic :=
    packet.right.right.right.right.right.right.left
  have equalityCont : Cont spectral analytic equality :=
    packet.right.right.right.right.right.right.right.left
  have topologicalCont : Cont chern characteristic topological :=
    packet.right.right.right.right.right.right.right.right.left
  have provenanceCont : Cont equality symbol provenance :=
    packet.right.right.right.right.right.right.right.right.right.left
  have endpointCont : Cont provenance topological endpoint :=
    packet.right.right.right.right.right.right.right.right.right.right.left
  have pkgSig : PkgSig bundle endpoint pkg :=
    packet.right.right.right.right.right.right.right.right.right.right.right
  have equalityUnary : UnaryHistory equality :=
    unary_cont_closed spectralUnary analyticUnary equalityCont
  have topologicalUnary : UnaryHistory topological :=
    unary_cont_closed chernUnary characteristicUnary topologicalCont
  have provenanceUnary : UnaryHistory provenance :=
    unary_cont_closed equalityUnary symbolUnary provenanceCont
  have endpointUnary : UnaryHistory endpoint :=
    unary_cont_closed provenanceUnary topologicalUnary endpointCont
  exact And.intro mUnary
    (And.intro symbolUnary
      (And.intro equalityUnary
        (And.intro topologicalUnary
          (And.intro provenanceUnary
            (And.intro endpointUnary
              (And.intro equalityCont
                (And.intro topologicalCont
                  (And.intro provenanceCont
                    (And.intro endpointCont
                      (And.intro pkgSig
                        (And.intro equalityCont topologicalCont)))))))))))

theorem AtiyahSingerIndexPairingCarrierPacket_spectral_chernweil_consumer_exhaustion
    [AskSetup] [PackageSetup]
    {m operator symbol spectral analytic chern characteristic topological equality provenance endpoint
      consumerLedger consumerEndpoint : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    AtiyahSingerIndexPairingCarrierPacket m operator symbol spectral analytic chern
        characteristic topological equality provenance endpoint bundle pkg ->
      Cont endpoint equality consumerLedger ->
        Cont consumerLedger symbol consumerEndpoint ->
          UnaryHistory consumerLedger ∧ UnaryHistory consumerEndpoint ∧
            hsame consumerLedger (append endpoint equality) ∧
              hsame consumerEndpoint (append (append endpoint equality) symbol) ∧
                hsame equality (append spectral analytic) ∧
                  hsame topological (append chern characteristic) ∧
                    hsame endpoint (append provenance topological) ∧
                      PkgSig bundle endpoint pkg := by
  intro packet consumerLedgerRow consumerEndpointRow
  have exactRows :=
    AtiyahSingerIndexPairingCarrierPacket_provenance_exactness
      (m := m) (operator := operator) (symbol := symbol) (spectral := spectral)
      (analytic := analytic) (chern := chern) (characteristic := characteristic)
      (topological := topological) (equality := equality) (provenance := provenance)
      (endpoint := endpoint) (bundle := bundle) (pkg := pkg) packet
  have symbolUnary : UnaryHistory symbol :=
    exactRows.right.left
  have equalityUnary : UnaryHistory equality :=
    exactRows.right.right.left
  have endpointUnary : UnaryHistory endpoint :=
    exactRows.right.right.right.right.right.left
  have consumerLedgerUnary : UnaryHistory consumerLedger :=
    unary_cont_closed endpointUnary equalityUnary consumerLedgerRow
  have consumerEndpointUnary : UnaryHistory consumerEndpoint :=
    unary_cont_closed consumerLedgerUnary symbolUnary consumerEndpointRow
  have consumerEndpointExact : hsame consumerEndpoint (append (append endpoint equality) symbol) := by
    cases consumerLedgerRow
    exact consumerEndpointRow
  exact And.intro consumerLedgerUnary
    (And.intro consumerEndpointUnary
      (And.intro consumerLedgerRow
        (And.intro consumerEndpointExact
          (And.intro exactRows.right.right.right.right.right.right.left
              (And.intro exactRows.right.right.right.right.right.right.right.left
                (And.intro exactRows.right.right.right.right.right.right.right.right.right.left
                  exactRows.right.right.right.right.right.right.right.right.right.right))))))

theorem AtiyahSingerIndexPairingCarrierPacket_namecert_obligation_surface
    [AskSetup] [PackageSetup]
    {m operator symbol spectral analytic chern characteristic topological equality provenance
      endpoint : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    AtiyahSingerIndexPairingCarrierPacket m operator symbol spectral analytic chern
        characteristic topological equality provenance endpoint bundle pkg ->
      SemanticNameCert (fun row : BHist => hsame row endpoint)
        (fun row : BHist => hsame row endpoint)
        (fun row : BHist => hsame row endpoint) hsame ∧
        UnaryHistory endpoint ∧ hsame equality (append spectral analytic) ∧
          hsame topological (append chern characteristic) ∧
            hsame provenance (append equality symbol) ∧ PkgSig bundle endpoint pkg := by
  intro packet
  have rows :=
    AtiyahSingerIndexPairingCarrierPacket_provenance_exactness
      (m := m) (operator := operator) (symbol := symbol) (spectral := spectral)
      (analytic := analytic) (chern := chern) (characteristic := characteristic)
      (topological := topological) (equality := equality) (provenance := provenance)
      (endpoint := endpoint) (bundle := bundle) (pkg := pkg) packet
  have endpointSelf : hsame endpoint endpoint :=
    hsame_refl endpoint
  have cert :
      SemanticNameCert (fun row : BHist => hsame row endpoint)
        (fun row : BHist => hsame row endpoint)
        (fun row : BHist => hsame row endpoint) hsame := {
    core := {
      carrier_inhabited := Exists.intro endpoint endpointSelf
      equiv_refl := by
        intro row _source
        exact hsame_refl row
      equiv_symm := by
        intro row other sameRows
        exact hsame_symm sameRows
      equiv_trans := by
        intro row other target sameLeft sameRight
        exact hsame_trans sameLeft sameRight
      carrier_respects_equiv := by
        intro row other sameRows rowSource
        exact hsame_trans (hsame_symm sameRows) rowSource
    }
    pattern_sound := by
      intro row source
      exact source
    ledger_sound := by
      intro row source
      exact source
  }
  exact And.intro cert
    (And.intro rows.right.right.right.right.right.left
      (And.intro rows.right.right.right.right.right.right.left
        (And.intro rows.right.right.right.right.right.right.right.left
          (And.intro rows.right.right.right.right.right.right.right.right.left
            rows.right.right.right.right.right.right.right.right.right.right))))

end BEDC.Derived.AtiyahSingerUp
