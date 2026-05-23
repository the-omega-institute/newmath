import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.Package
import BEDC.FKernel.Unary.History

namespace BEDC.Derived.RealDiagonalWindowCoverageUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def RealDiagonalWindowCoverageCarrier [AskSetup] [PackageSetup]
    (q w r d e transport route provenance nameCert : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  UnaryHistory q ∧ UnaryHistory w ∧ UnaryHistory r ∧ UnaryHistory d ∧
    UnaryHistory e ∧ UnaryHistory transport ∧ UnaryHistory route ∧
      UnaryHistory provenance ∧ Cont q w transport ∧ Cont w r route ∧
        Cont r d provenance ∧ Cont d e nameCert ∧ PkgSig bundle nameCert pkg

theorem RealDiagonalWindowCoverageCarrier_realup_handoff [AskSetup] [PackageSetup]
    {q w r d e transport route provenance nameCert : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    RealDiagonalWindowCoverageCarrier q w r d e transport route provenance nameCert
        bundle pkg →
      UnaryHistory q ∧ UnaryHistory w ∧ UnaryHistory r ∧ UnaryHistory d ∧
        UnaryHistory e ∧ Cont q w transport ∧ Cont w r route ∧
          Cont r d provenance ∧ Cont d e nameCert ∧ PkgSig bundle nameCert pkg := by
  intro packet
  have unaryD : UnaryHistory d := packet.right.right.right.left
  have unaryE : UnaryHistory e := packet.right.right.right.right.left
  have nameCertCont : Cont d e nameCert :=
    packet.right.right.right.right.right.right.right.right.right.right.right.left
  have pkgSig : PkgSig bundle nameCert pkg :=
    packet.right.right.right.right.right.right.right.right.right.right.right.right
  exact
    ⟨packet.left, packet.right.left, packet.right.right.left, unaryD, unaryE,
      packet.right.right.right.right.right.right.right.right.left,
      packet.right.right.right.right.right.right.right.right.right.left,
      packet.right.right.right.right.right.right.right.right.right.right.left,
      nameCertCont, pkgSig⟩

theorem RealDiagonalWindowCoverageCarrier_carrier_admission [AskSetup] [PackageSetup]
    {q w r d e transport route provenance nameCert : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    RealDiagonalWindowCoverageCarrier q w r d e transport route provenance nameCert
        bundle pkg →
      UnaryHistory q ∧ UnaryHistory w ∧ UnaryHistory r ∧ UnaryHistory d ∧
        UnaryHistory e ∧ UnaryHistory transport ∧ UnaryHistory route ∧
          UnaryHistory provenance ∧ UnaryHistory nameCert ∧ Cont q w transport ∧
            Cont w r route ∧ Cont r d provenance ∧ Cont d e nameCert ∧
              PkgSig bundle nameCert pkg := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle Pkg UnaryHistory
  intro packet
  cases packet with
  | intro unaryQ rest =>
      cases rest with
      | intro unaryW rest =>
          cases rest with
          | intro unaryR rest =>
              cases rest with
              | intro unaryD rest =>
                  cases rest with
                  | intro unaryE rest =>
                      cases rest with
                      | intro unaryTransport rest =>
                          cases rest with
                          | intro unaryRoute rest =>
                              cases rest with
                              | intro unaryProvenance rest =>
                                  cases rest with
                                  | intro qToW rest =>
                                      cases rest with
                                      | intro wToR rest =>
                                          cases rest with
                                          | intro rToD rest =>
                                              cases rest with
                                              | intro dToE pkgSig =>
                                                  have unaryNameCert :
                                                      UnaryHistory nameCert :=
                                                    unary_cont_closed unaryD unaryE dToE
                                                  exact
                                                    ⟨unaryQ, unaryW, unaryR, unaryD, unaryE,
                                                      unaryTransport, unaryRoute,
                                                      unaryProvenance, unaryNameCert, qToW,
                                                      wToR, rToD, dToE, pkgSig⟩

end BEDC.Derived.RealDiagonalWindowCoverageUp
