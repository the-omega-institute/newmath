import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.Package
import BEDC.FKernel.Unary.History

namespace BEDC.Derived.FftUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def FftBHistSourceCore
    (complex fourier stage schedule factor ledger endpoint : BHist)
    (bundle : ProbeBundle BHist) : Prop :=
  UnaryHistory complex ∧ UnaryHistory fourier ∧ UnaryHistory factor ∧ InBundle stage bundle ∧
    Cont complex fourier schedule ∧ Cont schedule factor ledger ∧ Cont ledger stage endpoint

theorem FftBHistSourcePacket_butterfly_schedule_obligation
    {complex fourier stage schedule factor ledger endpoint : BHist}
    {bundle : ProbeBundle BHist} :
    FftBHistSourceCore complex fourier stage schedule factor ledger endpoint bundle ->
      InBundle stage bundle ∧ Cont complex fourier schedule ∧ Cont schedule factor ledger ∧
        Cont ledger stage endpoint ∧ UnaryHistory schedule ∧ UnaryHistory ledger := by
  intro packet
  have scheduleUnary : UnaryHistory schedule :=
    unary_cont_closed packet.left packet.right.left packet.right.right.right.right.left
  have ledgerUnary : UnaryHistory ledger :=
    unary_cont_closed scheduleUnary packet.right.right.left
      packet.right.right.right.right.right.left
  exact
    ⟨packet.right.right.right.left, packet.right.right.right.right.left,
      packet.right.right.right.right.right.left, packet.right.right.right.right.right.right,
      scheduleUnary, ledgerUnary⟩

def FftBHistSourcePacket [AskSetup] [PackageSetup]
    (complex fourier stage butterfly factorization ledger endpoint : BHist)
    (stageName : ProbeName) (schedule : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  InBundle stageName schedule ∧
    UnaryHistory complex ∧ UnaryHistory fourier ∧ UnaryHistory butterfly ∧
      UnaryHistory factorization ∧
      Cont complex fourier stage ∧
        Cont stage butterfly ledger ∧ Cont ledger factorization endpoint ∧
          PkgSig schedule endpoint pkg

theorem FftBHistSourcePacket_carrier_butterfly_obligation [AskSetup] [PackageSetup]
    {complex fourier stage butterfly factorization ledger endpoint : BHist}
    {stageName : ProbeName} {schedule : ProbeBundle ProbeName} {pkg : Pkg} :
    FftBHistSourcePacket complex fourier stage butterfly factorization ledger endpoint
        stageName schedule pkg ->
      InBundle stageName schedule ∧ UnaryHistory complex ∧ UnaryHistory fourier ∧
        UnaryHistory stage ∧ UnaryHistory butterfly ∧ UnaryHistory ledger ∧ UnaryHistory endpoint ∧
          Cont complex fourier stage ∧ Cont stage butterfly ledger ∧
            Cont ledger factorization endpoint ∧ PkgSig schedule endpoint pkg := by
  intro packet
  have fourierUnary : UnaryHistory fourier := packet.right.right.left
  have stageUnary : UnaryHistory stage :=
    unary_cont_closed packet.right.left fourierUnary packet.right.right.right.right.right.left
  have butterflyUnary : UnaryHistory butterfly := packet.right.right.right.left
  have ledgerUnary : UnaryHistory ledger :=
    unary_cont_closed stageUnary butterflyUnary packet.right.right.right.right.right.right.left
  have factorizationUnary : UnaryHistory factorization := packet.right.right.right.right.left
  have endpointUnary : UnaryHistory endpoint :=
    unary_cont_closed ledgerUnary factorizationUnary
      packet.right.right.right.right.right.right.right.left
  exact
    ⟨packet.left, packet.right.left, fourierUnary, stageUnary, butterflyUnary, ledgerUnary,
      endpointUnary, packet.right.right.right.right.right.left,
      packet.right.right.right.right.right.right.left,
      packet.right.right.right.right.right.right.right.left,
      packet.right.right.right.right.right.right.right.right⟩

theorem FftBHistSourcePacket_factorization_classifier_stability [AskSetup] [PackageSetup]
    {complex fourier stage butterfly factorization factorization' ledger ledger'
      endpoint endpoint' : BHist}
    {stageName : ProbeName} {schedule : ProbeBundle ProbeName} {pkg : Pkg} :
    FftBHistSourcePacket complex fourier stage butterfly factorization ledger endpoint
        stageName schedule pkg ->
      hsame factorization factorization' ->
        Cont stage butterfly ledger' ->
          Cont ledger' factorization' endpoint' ->
            PkgSig schedule endpoint' pkg ->
              FftBHistSourcePacket complex fourier stage butterfly factorization' ledger'
                  endpoint' stageName schedule pkg ∧
                hsame ledger ledger' ∧ hsame endpoint endpoint' := by
  intro packet sameFactorization ledgerCont' endpointCont' pkgSig'
  have factorizationUnary' : UnaryHistory factorization' :=
    unary_transport packet.right.right.right.right.left sameFactorization
  have sameLedger : hsame ledger ledger' :=
    cont_respects_hsame (hsame_refl stage) (hsame_refl butterfly)
      packet.right.right.right.right.right.right.left ledgerCont'
  have sameEndpoint : hsame endpoint endpoint' :=
    cont_respects_hsame sameLedger sameFactorization
      packet.right.right.right.right.right.right.right.left endpointCont'
  exact
    ⟨⟨packet.left, packet.right.left, packet.right.right.left, packet.right.right.right.left,
        factorizationUnary', packet.right.right.right.right.right.left, ledgerCont',
        endpointCont', pkgSig'⟩,
      sameLedger, sameEndpoint⟩

end BEDC.Derived.FftUp
