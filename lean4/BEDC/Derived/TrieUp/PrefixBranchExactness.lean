import BEDC.Derived.TrieUp

namespace BEDC.Derived.TrieUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem TrieSourcePacket_prefix_branch_exactness [AskSetup] [PackageSetup]
    {key payload depth branch provenance route payloadRoute branchRoute branchRead
      publicExport : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    TrieSourcePacket key payload depth branch provenance route payloadRoute branchRoute
        bundle pkg ->
      Cont branch payloadRoute branchRead ->
        Cont branchRoute provenance publicExport ->
          PkgSig bundle publicExport pkg ->
            hsame branchRoute branchRead ∧ UnaryHistory branchRead ∧
              UnaryHistory publicExport ∧ UnaryHistory key ∧ UnaryHistory depth ∧
                UnaryHistory branch ∧ Cont key depth route ∧
                  Cont branchRoute provenance publicExport ∧ PkgSig bundle provenance pkg ∧
                    PkgSig bundle publicExport pkg := by
  intro packet branchReadRow publicExportRow publicExportPkg
  obtain ⟨keyUnary, payloadUnary, depthUnary, branchUnary, provenanceUnary, routeRow,
    _provenanceRow, payloadRouteRow, branchRouteRow, provenancePkg⟩ := packet
  have payloadRouteUnary : UnaryHistory payloadRoute :=
    unary_cont_closed payloadUnary depthUnary payloadRouteRow
  have branchRouteUnary : UnaryHistory branchRoute :=
    unary_cont_closed branchUnary payloadRouteUnary branchRouteRow
  have sameBranchRead : hsame branchRoute branchRead :=
    cont_deterministic branchRouteRow branchReadRow
  have branchReadUnary : UnaryHistory branchRead :=
    unary_cont_closed branchUnary payloadRouteUnary branchReadRow
  have publicExportUnary : UnaryHistory publicExport :=
    unary_cont_closed branchRouteUnary provenanceUnary publicExportRow
  exact
    ⟨sameBranchRead, branchReadUnary, publicExportUnary, keyUnary, depthUnary,
      branchUnary, routeRow, publicExportRow, provenancePkg, publicExportPkg⟩

end BEDC.Derived.TrieUp
