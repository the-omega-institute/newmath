import BEDC.Derived.TrieUp

namespace BEDC.Derived.TrieUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem TrieSourcePacket_namecert_obligation_surface [AskSetup] [PackageSetup]
    {key payload depth branch provenance route payloadRoute branchRoute consumer lookupRead
      terminalRead branchRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    TrieSourcePacket key payload depth branch provenance route payloadRoute branchRoute
        bundle pkg ->
      Cont provenance payloadRoute consumer ->
        Cont payloadRoute provenance lookupRead ->
          Cont payload provenance terminalRead ->
            Cont branch provenance branchRead ->
              PkgSig bundle consumer pkg ->
                PkgSig bundle lookupRead pkg ->
                  PkgSig bundle terminalRead pkg ->
                    PkgSig bundle branchRead pkg ->
                      (UnaryHistory route ∧ UnaryHistory payloadRoute ∧
                          UnaryHistory branchRoute ∧ UnaryHistory provenance ∧
                            Cont key depth route ∧ Cont route branch provenance ∧
                              PkgSig bundle provenance pkg) ∧
                        (UnaryHistory consumer ∧ PkgSig bundle consumer pkg) ∧
                          (UnaryHistory lookupRead ∧ PkgSig bundle lookupRead pkg) ∧
                            (UnaryHistory terminalRead ∧ UnaryHistory branchRead ∧
                              PkgSig bundle terminalRead pkg ∧ PkgSig bundle branchRead pkg) := by
  intro packet consumerRow lookupRow terminalRow branchRow consumerPkg lookupPkg terminalPkg
    branchPkg
  obtain ⟨keyUnary, payloadUnary, depthUnary, branchUnary, provenanceUnary, routeRow,
    provenanceRow, payloadRouteRow, branchRouteRow, provenancePkg⟩ := packet
  have routeUnary : UnaryHistory route :=
    unary_cont_closed keyUnary depthUnary routeRow
  have payloadRouteUnary : UnaryHistory payloadRoute :=
    unary_cont_closed payloadUnary depthUnary payloadRouteRow
  have branchRouteUnary : UnaryHistory branchRoute :=
    unary_cont_closed branchUnary payloadRouteUnary branchRouteRow
  have consumerUnary : UnaryHistory consumer :=
    unary_cont_closed provenanceUnary payloadRouteUnary consumerRow
  have lookupUnary : UnaryHistory lookupRead :=
    unary_cont_closed payloadRouteUnary provenanceUnary lookupRow
  have terminalUnary : UnaryHistory terminalRead :=
    unary_cont_closed payloadUnary provenanceUnary terminalRow
  have branchReadUnary : UnaryHistory branchRead :=
    unary_cont_closed branchUnary provenanceUnary branchRow
  exact
    ⟨⟨routeUnary, payloadRouteUnary, branchRouteUnary, provenanceUnary, routeRow, provenanceRow,
        provenancePkg⟩,
      ⟨consumerUnary, consumerPkg⟩,
      ⟨lookupUnary, lookupPkg⟩,
      ⟨terminalUnary, branchReadUnary, terminalPkg, branchPkg⟩⟩

end BEDC.Derived.TrieUp
