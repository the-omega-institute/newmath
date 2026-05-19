import BEDC.Derived.ZnormalUp.RootTotalHostRefusalLedger
import BEDC.FKernel.Cont.Cancellation

namespace BEDC.Derived.ZnormalUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem ZnormalRootRefusalLedgerSeparation [AskSetup] [PackageSetup]
    {typed fuel terminal normal continuation transports routes provenance name terminalRead rootRead
      downstream hostTail : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ZnormalPacket typed fuel terminal normal continuation transports routes provenance name
        bundle pkg →
      Cont typed fuel terminalRead →
        Cont terminalRead normal rootRead →
          Cont rootRead transports downstream →
            PkgSig bundle downstream pkg →
              SemanticNameCert
                  (fun row : BHist => hsame row downstream ∧ UnaryHistory row)
                  (fun row : BHist =>
                    hsame row typed ∨ hsame row terminalRead ∨ hsame row rootRead ∨
                      hsame row downstream)
                  (fun row : BHist =>
                    hsame row downstream ∧ PkgSig bundle downstream pkg)
                  hsame ∧
                hsame terminalRead terminal ∧ hsame rootRead continuation ∧
                  UnaryHistory terminalRead ∧ UnaryHistory rootRead ∧
                    UnaryHistory downstream ∧ PkgSig bundle name pkg ∧
                      PkgSig bundle provenance pkg ∧ PkgSig bundle downstream pkg ∧
                        (Cont downstream (BHist.e0 hostTail) typed → False) ∧
                          (Cont downstream (BHist.e1 hostTail) typed → False) := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame SemanticNameCert UnaryHistory
  intro packet typedFuelTerminalRead terminalReadNormalRootRead rootReadTransportsDownstream
    downstreamPkg
  have ledger :=
    ZnormalPacket_root_total_host_refusal_ledger
      (typed := typed) (fuel := fuel) (terminal := terminal) (normal := normal)
      (continuation := continuation) (transports := transports) (routes := routes)
      (provenance := provenance) (name := name) (terminalRead := terminalRead)
      (rootRead := rootRead) (downstream := downstream) (bundle := bundle) (pkg := pkg)
      packet typedFuelTerminalRead terminalReadNormalRootRead rootReadTransportsDownstream
      downstreamPkg
  have typedToDownstream : Cont typed (append fuel (append normal transports)) downstream := by
    cases typedFuelTerminalRead
    cases terminalReadNormalRootRead
    cases rootReadTransportsDownstream
    exact (append_assoc (append typed fuel) normal transports).trans
      (append_assoc typed fuel (append normal transports))
  have e0Refusal : Cont downstream (BHist.e0 hostTail) typed → False :=
    fun back => cont_mutual_extension_right_tail_absurd.left typedToDownstream back
  have e1Refusal : Cont downstream (BHist.e1 hostTail) typed → False :=
    fun back => cont_mutual_extension_right_tail_absurd.right typedToDownstream back
  exact
    ⟨ledger.left, ledger.right.left, ledger.right.right.left, ledger.right.right.right.left,
      ledger.right.right.right.right.left, ledger.right.right.right.right.right.left,
      ledger.right.right.right.right.right.right.left,
      ledger.right.right.right.right.right.right.right.left,
      ledger.right.right.right.right.right.right.right.right, e0Refusal, e1Refusal⟩

end BEDC.Derived.ZnormalUp
