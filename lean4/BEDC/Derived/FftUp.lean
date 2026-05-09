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

end BEDC.Derived.FftUp
