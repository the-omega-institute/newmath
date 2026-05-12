import BEDC.Derived.TrieUp

namespace BEDC.Derived.TrieUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem TrieTerminalPacket_prefix_readback_coverage [AskSetup] [PackageSetup]
    {key terminal transport route branch provenance cert pref terminalRead routedRead
      readback : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    TrieTerminalPacket key terminal transport route branch provenance cert bundle pkg ->
      UnaryHistory pref ->
        hsame key pref ->
          Cont pref terminal terminalRead ->
            Cont terminalRead route routedRead ->
              Cont routedRead provenance readback ->
                PkgSig bundle readback pkg ->
                  UnaryHistory pref ∧ UnaryHistory terminalRead ∧ UnaryHistory routedRead ∧
                    UnaryHistory readback ∧ hsame transport terminalRead ∧
                      hsame branch routedRead ∧ hsame cert readback ∧
                        PkgSig bundle readback pkg := by
  intro packet prefUnary sameKey terminalReadRow routedReadRow readbackRow readbackPkg
  obtain ⟨_keyUnary, terminalUnary, routeUnary, provenanceUnary, transportRow, branchRow,
    certRow, _packetPkg⟩ := packet
  have terminalReadUnary : UnaryHistory terminalRead :=
    unary_cont_closed prefUnary terminalUnary terminalReadRow
  have sameTransport : hsame transport terminalRead :=
    cont_respects_hsame sameKey (hsame_refl terminal) transportRow terminalReadRow
  have routedReadUnary : UnaryHistory routedRead :=
    unary_cont_closed terminalReadUnary routeUnary routedReadRow
  have sameBranch : hsame branch routedRead :=
    cont_respects_hsame sameTransport (hsame_refl route) branchRow routedReadRow
  have readbackUnary : UnaryHistory readback :=
    unary_cont_closed routedReadUnary provenanceUnary readbackRow
  have sameCert : hsame cert readback :=
    cont_respects_hsame sameBranch (hsame_refl provenance) certRow readbackRow
  exact
    ⟨prefUnary, terminalReadUnary, routedReadUnary, readbackUnary, sameTransport,
      sameBranch, sameCert, readbackPkg⟩

end BEDC.Derived.TrieUp
