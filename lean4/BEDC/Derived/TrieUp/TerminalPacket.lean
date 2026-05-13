import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.TrieUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def TrieTerminalPacket [AskSetup] [PackageSetup]
    (key terminal transport route branch provenance cert : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  UnaryHistory key ∧ UnaryHistory terminal ∧ UnaryHistory route ∧ UnaryHistory provenance ∧
    Cont key terminal transport ∧ Cont transport route branch ∧ Cont branch provenance cert ∧
      PkgSig bundle cert pkg

theorem TrieTerminalPacket_boolean_key_path_ledger_coverage [AskSetup] [PackageSetup]
    {key terminal transport route branch provenance cert key' terminal' transport' route' branch'
      provenance' cert' : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    TrieTerminalPacket key terminal transport route branch provenance cert bundle pkg ->
      TrieTerminalPacket key' terminal' transport' route' branch' provenance' cert' bundle pkg ->
        hsame key key' ->
          hsame terminal terminal' ->
            hsame route route' ->
              hsame provenance provenance' ->
                  hsame transport transport' ∧ hsame branch branch' ∧ hsame cert cert' := by
    intro packet packet' sameKey sameTerminal sameRoute sameProvenance
    obtain ⟨_keyUnary, _terminalUnary, _routeUnary, _provenanceUnary, transportRow,
      branchRow, certRow, _pkgSig⟩ := packet
    obtain ⟨_keyUnary', _terminalUnary', _routeUnary', _provenanceUnary', transportRow',
      branchRow', certRow', _pkgSig'⟩ := packet'
    have sameTransport : hsame transport transport' :=
      cont_respects_hsame sameKey sameTerminal transportRow transportRow'
    have sameBranch : hsame branch branch' :=
      cont_respects_hsame sameTransport sameRoute branchRow branchRow'
    have sameCert : hsame cert cert' :=
      cont_respects_hsame sameBranch sameProvenance certRow certRow'
    exact ⟨sameTransport, sameBranch, sameCert⟩

theorem TrieTerminalPacket_terminal_prefix_readback_coverage [AskSetup] [PackageSetup]
    {key terminal transport route branch provenance cert «prefix» readback consumer : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    TrieTerminalPacket key terminal transport route branch provenance cert bundle pkg ->
      UnaryHistory «prefix» ->
        Cont «prefix» branch readback ->
          Cont readback cert consumer ->
            PkgSig bundle consumer pkg ->
              UnaryHistory key ∧ UnaryHistory terminal ∧ UnaryHistory branch ∧
                UnaryHistory cert ∧ UnaryHistory «prefix» ∧ UnaryHistory readback ∧
                  UnaryHistory consumer ∧ hsame transport (append key terminal) ∧
                    hsame branch (append transport route) ∧
                      hsame cert (append branch provenance) ∧ Cont «prefix» branch readback ∧
                        Cont readback cert consumer ∧ PkgSig bundle consumer pkg := by
  intro packet prefixUnary readbackRow consumerRow consumerPkg
  obtain ⟨keyUnary, terminalUnary, routeUnary, provenanceUnary, transportRow, branchRow,
    certRow, _packetPkg⟩ := packet
  have transportUnary : UnaryHistory transport :=
    unary_cont_closed keyUnary terminalUnary transportRow
  have branchUnary : UnaryHistory branch :=
    unary_cont_closed transportUnary routeUnary branchRow
  have certUnary : UnaryHistory cert :=
    unary_cont_closed branchUnary provenanceUnary certRow
  have readbackUnary : UnaryHistory readback :=
    unary_cont_closed prefixUnary branchUnary readbackRow
  have consumerUnary : UnaryHistory consumer :=
    unary_cont_closed readbackUnary certUnary consumerRow
  exact
    ⟨keyUnary, terminalUnary, branchUnary, certUnary, prefixUnary, readbackUnary, consumerUnary,
      transportRow, branchRow, certRow, readbackRow, consumerRow, consumerPkg⟩

end BEDC.Derived.TrieUp
