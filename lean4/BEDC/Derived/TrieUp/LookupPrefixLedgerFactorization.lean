import BEDC.Derived.TrieUp

namespace BEDC.Derived.TrieUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem TrieSourcePacket_lookup_prefix_ledger_factorization [AskSetup] [PackageSetup]
    {key payload depth branch provenance route payloadRoute branchRoute pref terminalRead
      branchRead lookupRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    TrieSourcePacket key payload depth branch provenance route payloadRoute branchRoute bundle
        pkg ->
      UnaryHistory pref -> Cont pref payload terminalRead -> Cont pref branch branchRead ->
        Cont terminalRead branchRead lookupRead -> PkgSig bundle lookupRead pkg ->
          UnaryHistory terminalRead ∧ UnaryHistory branchRead ∧ UnaryHistory lookupRead ∧
            Cont pref payload terminalRead ∧ Cont pref branch branchRead ∧
              Cont terminalRead branchRead lookupRead ∧ PkgSig bundle lookupRead pkg := by
  intro packet prefUnary terminalReadRow branchReadRow lookupReadRow lookupPkg
  obtain ⟨_keyUnary, payloadUnary, _depthUnary, branchUnary, _provenanceUnary, _routeRow,
    _provenanceRow, _payloadRouteRow, _branchRouteRow, _packetPkg⟩ := packet
  have terminalReadUnary : UnaryHistory terminalRead :=
    unary_cont_closed prefUnary payloadUnary terminalReadRow
  have branchReadUnary : UnaryHistory branchRead :=
    unary_cont_closed prefUnary branchUnary branchReadRow
  have lookupReadUnary : UnaryHistory lookupRead :=
    unary_cont_closed terminalReadUnary branchReadUnary lookupReadRow
  exact
    ⟨terminalReadUnary, branchReadUnary, lookupReadUnary, terminalReadRow, branchReadRow,
      lookupReadRow, lookupPkg⟩

end BEDC.Derived.TrieUp
