import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.ControlControllabilityUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def ControlControllabilityCarrier [AskSetup] [PackageSetup]
    (state input transition control horizon columns matrix contRows endpoint : BHist)
    (probe : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  UnaryHistory state ∧ UnaryHistory input ∧ UnaryHistory transition ∧
    UnaryHistory control ∧ UnaryHistory horizon ∧ UnaryHistory columns ∧
      UnaryHistory matrix ∧ UnaryHistory contRows ∧ UnaryHistory endpoint ∧
        Cont transition control columns ∧ Cont columns matrix endpoint ∧
          Cont contRows horizon endpoint ∧ PkgSig probe endpoint pkg

theorem ControlControllabilityCarrier_namecert_obligation_surface [AskSetup] [PackageSetup]
    {state input transition control horizon columns matrix contRows endpoint : BHist}
    {probe : ProbeBundle ProbeName} {pkg : Pkg} :
    ControlControllabilityCarrier state input transition control horizon columns matrix contRows
        endpoint probe pkg ->
      SemanticNameCert (fun h : BHist => hsame h endpoint)
          (fun h : BHist => hsame h endpoint) (fun h : BHist => hsame h endpoint)
          hsame ∧
        Cont transition control columns ∧ Cont columns matrix endpoint ∧
          Cont contRows horizon endpoint ∧ PkgSig probe endpoint pkg := by
  intro carrier
  have cert :
      SemanticNameCert (fun h : BHist => hsame h endpoint)
          (fun h : BHist => hsame h endpoint) (fun h : BHist => hsame h endpoint)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro endpoint (hsame_refl endpoint)
      equiv_refl := by
        intro row _source
        exact hsame_refl row
      equiv_symm := by
        intro row row' same
        exact hsame_symm same
      equiv_trans := by
        intro row row' row'' sameLeft sameRight
        exact hsame_trans sameLeft sameRight
      carrier_respects_equiv := by
        intro row row' sameRows sourceRow
        exact hsame_trans (hsame_symm sameRows) sourceRow
    }
    pattern_sound := by
      intro _row sourceRow
      exact sourceRow
    ledger_sound := by
      intro _row sourceRow
      exact sourceRow
  }
  exact And.intro cert
    (And.intro carrier.right.right.right.right.right.right.right.right.right.left
      (And.intro carrier.right.right.right.right.right.right.right.right.right.right.left
        (And.intro carrier.right.right.right.right.right.right.right.right.right.right.right.left
          carrier.right.right.right.right.right.right.right.right.right.right.right.right)))

def ControlControllabilityReachabilityPacket [AskSetup] [PackageSetup]
    (state input transition control horizon firstColumn reachability provenance endpoint : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  UnaryHistory state ∧ UnaryHistory input ∧ UnaryHistory transition ∧
    UnaryHistory control ∧ UnaryHistory horizon ∧ UnaryHistory provenance ∧
      Cont control horizon firstColumn ∧ Cont firstColumn transition reachability ∧
        Cont reachability provenance endpoint ∧ PkgSig bundle endpoint pkg

theorem ControlControllabilityReachabilityPacket_reachability_ledger [AskSetup]
    [PackageSetup] {bundle : ProbeBundle ProbeName} {pkg : Pkg}
    {state input transition control horizon firstColumn reachability provenance endpoint : BHist} :
    ControlControllabilityReachabilityPacket state input transition control horizon firstColumn
        reachability provenance endpoint bundle pkg ->
      UnaryHistory state ∧ UnaryHistory input ∧ UnaryHistory transition ∧
        UnaryHistory control ∧ UnaryHistory horizon ∧ UnaryHistory firstColumn ∧
          UnaryHistory reachability ∧ hsame firstColumn (append control horizon) ∧
            hsame reachability (append firstColumn transition) ∧ PkgSig bundle endpoint pkg := by
  intro packet
  have stateUnary : UnaryHistory state :=
    packet.left
  have inputUnary : UnaryHistory input :=
    packet.right.left
  have transitionUnary : UnaryHistory transition :=
    packet.right.right.left
  have controlUnary : UnaryHistory control :=
    packet.right.right.right.left
  have horizonUnary : UnaryHistory horizon :=
    packet.right.right.right.right.left
  have firstColumnRow : Cont control horizon firstColumn :=
    packet.right.right.right.right.right.right.left
  have reachabilityRow : Cont firstColumn transition reachability :=
    packet.right.right.right.right.right.right.right.left
  have pkgSig : PkgSig bundle endpoint pkg :=
    packet.right.right.right.right.right.right.right.right.right
  have firstColumnUnary : UnaryHistory firstColumn :=
    unary_cont_closed controlUnary horizonUnary firstColumnRow
  have reachabilityUnary : UnaryHistory reachability :=
    unary_cont_closed firstColumnUnary transitionUnary reachabilityRow
  exact And.intro stateUnary
    (And.intro inputUnary
      (And.intro transitionUnary
        (And.intro controlUnary
          (And.intro horizonUnary
            (And.intro firstColumnUnary
              (And.intro reachabilityUnary
                (And.intro firstColumnRow (And.intro reachabilityRow pkgSig))))))))

theorem ControlControllabilityReachabilityPacket_consumer_boundary [AskSetup]
    [PackageSetup] {bundle : ProbeBundle ProbeName} {pkg : Pkg}
    {state input transition control horizon firstColumn reachability provenance endpoint : BHist} :
    ControlControllabilityReachabilityPacket state input transition control horizon firstColumn
        reachability provenance endpoint bundle pkg ->
      SemanticNameCert
          (fun row : BHist =>
            ControlControllabilityReachabilityPacket state input transition control horizon
              firstColumn reachability provenance endpoint bundle pkg ∧ hsame row endpoint)
          (fun row : BHist =>
            ControlControllabilityReachabilityPacket state input transition control horizon
              firstColumn reachability provenance endpoint bundle pkg ∧ hsame row endpoint)
          (fun row : BHist =>
            ControlControllabilityReachabilityPacket state input transition control horizon
              firstColumn reachability provenance endpoint bundle pkg ∧ hsame row endpoint)
          hsame ∧
        UnaryHistory state ∧ UnaryHistory input ∧ UnaryHistory transition ∧
          UnaryHistory control ∧ UnaryHistory horizon ∧ UnaryHistory firstColumn ∧
            UnaryHistory reachability ∧ Cont control horizon firstColumn ∧
              Cont firstColumn transition reachability ∧
                Cont reachability provenance endpoint ∧ PkgSig bundle endpoint pkg := by
  intro packet
  have cert :
      SemanticNameCert
          (fun row : BHist =>
            ControlControllabilityReachabilityPacket state input transition control horizon
              firstColumn reachability provenance endpoint bundle pkg ∧ hsame row endpoint)
          (fun row : BHist =>
            ControlControllabilityReachabilityPacket state input transition control horizon
              firstColumn reachability provenance endpoint bundle pkg ∧ hsame row endpoint)
          (fun row : BHist =>
            ControlControllabilityReachabilityPacket state input transition control horizon
              firstColumn reachability provenance endpoint bundle pkg ∧ hsame row endpoint)
          hsame := {
    core := {
      carrier_inhabited :=
        Exists.intro endpoint (And.intro packet (hsame_refl endpoint))
      equiv_refl := by
        intro row _source
        exact hsame_refl row
      equiv_symm := by
        intro _row _row' same
        exact hsame_symm same
      equiv_trans := by
        intro _row _row' _row'' sameLeft sameRight
        exact hsame_trans sameLeft sameRight
      carrier_respects_equiv := by
        intro _row _row' same source
        exact And.intro source.left (hsame_trans (hsame_symm same) source.right)
    }
    pattern_sound := by
      intro _row source
      exact source
    ledger_sound := by
      intro _row source
      exact source
  }
  have firstColumnUnary : UnaryHistory firstColumn :=
    unary_cont_closed packet.right.right.right.left packet.right.right.right.right.left
      packet.right.right.right.right.right.right.left
  have reachabilityUnary : UnaryHistory reachability :=
    unary_cont_closed firstColumnUnary packet.right.right.left
      packet.right.right.right.right.right.right.right.left
  exact And.intro cert
    (And.intro packet.left
      (And.intro packet.right.left
        (And.intro packet.right.right.left
          (And.intro packet.right.right.right.left
            (And.intro packet.right.right.right.right.left
              (And.intro firstColumnUnary
                (And.intro reachabilityUnary
                  (And.intro packet.right.right.right.right.right.right.left
                    (And.intro packet.right.right.right.right.right.right.right.left
                      (And.intro packet.right.right.right.right.right.right.right.right.left
                        packet.right.right.right.right.right.right.right.right.right))))))))))

end BEDC.Derived.ControlControllabilityUp
