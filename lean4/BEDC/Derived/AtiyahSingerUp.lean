import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.AtiyahSingerUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
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

end BEDC.Derived.AtiyahSingerUp
