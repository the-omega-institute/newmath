import BEDC.Derived.TrieUp

namespace BEDC.Derived.TrieUp.TerminalPrefixReadback

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem TrieSourcePacket_terminal_prefix_readback_coverage [AskSetup] [PackageSetup]
    {key payload depth branch provenance route payloadRoute branchRoute pref branchTag readback
      terminal : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    TrieSourcePacket key payload depth branch provenance route payloadRoute branchRoute
        bundle pkg ->
      UnaryHistory pref ->
        UnaryHistory branchTag ->
          Cont pref branchTag readback ->
            Cont readback provenance terminal ->
              PkgSig bundle terminal pkg ->
                (pref = BHist.Empty ∨
                    ∃ tail : BHist, pref = BHist.e1 tail ∧ UnaryHistory tail) ∧
                  UnaryHistory key ∧ UnaryHistory payload ∧ UnaryHistory depth ∧
                    UnaryHistory branch ∧ UnaryHistory readback ∧ UnaryHistory terminal ∧
                      Cont pref branchTag readback ∧ Cont readback provenance terminal ∧
                        PkgSig bundle terminal pkg := by
  intro packet prefUnary branchTagUnary branchRead terminalRow terminalPkg
  obtain ⟨prefixSplit, readbackUnary, terminalUnary, keyUnary, branchUnary, depthUnary,
    branchReadRow, terminalReadRow, terminalPkgRow⟩ :=
    TrieSourcePacket_prefix_branch_consumer_exhaustion packet prefUnary branchTagUnary
      branchRead terminalRow terminalPkg
  obtain ⟨_keyUnary, payloadUnary, _depthUnary, _branchUnary, _provenanceUnary,
    _routeRow, _provenanceRow, _payloadRouteRow, _branchRouteRow, _packetPkg⟩ := packet
  exact
    ⟨prefixSplit, keyUnary, payloadUnary, depthUnary, branchUnary, readbackUnary,
      terminalUnary, branchReadRow, terminalReadRow, terminalPkgRow⟩

end BEDC.Derived.TrieUp.TerminalPrefixReadback
