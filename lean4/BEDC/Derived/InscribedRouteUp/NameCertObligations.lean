import BEDC.Derived.InscribedRouteUp.TasteGate
import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.InscribedRouteUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem InscribedRouteNameCertObligations [AskSetup] [PackageSetup]
    {sourceScope visibleGap namedStatement routeRow acceptance downstream ledger provenance
      localName acceptedRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    UnaryHistory routeRow →
      UnaryHistory sourceScope →
        UnaryHistory visibleGap →
          UnaryHistory downstream →
            UnaryHistory provenance →
              Cont routeRow sourceScope namedStatement →
                Cont namedStatement visibleGap acceptance →
                  Cont acceptance downstream acceptedRead →
                    PkgSig bundle provenance pkg →
                      PkgSig bundle acceptedRead pkg →
                        SemanticNameCert
                            (fun row : BHist => hsame row acceptedRead ∧ UnaryHistory row)
                            (fun row : BHist =>
                              hsame row sourceScope ∨ hsame row visibleGap ∨
                                hsame row namedStatement ∨ hsame row routeRow ∨
                                  hsame row acceptance ∨ hsame row downstream ∨
                                    hsame row ledger ∨ hsame row acceptedRead)
                            (fun row : BHist =>
                              UnaryHistory row ∧ Cont routeRow sourceScope namedStatement ∧
                                Cont namedStatement visibleGap acceptance ∧
                                  Cont acceptance downstream acceptedRead ∧
                                    PkgSig bundle acceptedRead pkg ∧
                                      PkgSig bundle provenance pkg)
                            hsame ∧
                          UnaryHistory namedStatement ∧ UnaryHistory acceptance ∧
                            UnaryHistory acceptedRead := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle PkgSig SemanticNameCert hsame UnaryHistory
  intro routeUnary sourceUnary gapUnary downstreamUnary _provenanceUnary
    routeSourceStatement statementGapAcceptance acceptanceDownstreamAccepted provenancePkg
    acceptedPkg
  have statementUnary : UnaryHistory namedStatement :=
    unary_cont_closed routeUnary sourceUnary routeSourceStatement
  have acceptanceUnary : UnaryHistory acceptance :=
    unary_cont_closed statementUnary gapUnary statementGapAcceptance
  have acceptedUnary : UnaryHistory acceptedRead :=
    unary_cont_closed acceptanceUnary downstreamUnary acceptanceDownstreamAccepted
  have sourceAccepted :
      (fun row : BHist => hsame row acceptedRead ∧ UnaryHistory row) acceptedRead := by
    exact ⟨hsame_refl acceptedRead, acceptedUnary⟩
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row acceptedRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row sourceScope ∨ hsame row visibleGap ∨ hsame row namedStatement ∨
              hsame row routeRow ∨ hsame row acceptance ∨ hsame row downstream ∨
                hsame row ledger ∨ hsame row acceptedRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont routeRow sourceScope namedStatement ∧
              Cont namedStatement visibleGap acceptance ∧
                Cont acceptance downstream acceptedRead ∧ PkgSig bundle acceptedRead pkg ∧
                  PkgSig bundle provenance pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro acceptedRead sourceAccepted
      equiv_refl := by
        intro row _source
        exact hsame_refl row
      equiv_symm := by
        intro _row _other sameRows
        exact hsame_symm sameRows
      equiv_trans := by
        intro _row _middle _other sameLeft sameRight
        exact hsame_trans sameLeft sameRight
      carrier_respects_equiv := by
        intro _row _other sameRows source
        exact
          ⟨hsame_trans (hsame_symm sameRows) source.left,
            unary_transport source.right sameRows⟩
    }
    pattern_sound := by
      intro _row source
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr source.left))))))
    ledger_sound := by
      intro _row source
      exact
        ⟨source.right, routeSourceStatement, statementGapAcceptance,
          acceptanceDownstreamAccepted, acceptedPkg, provenancePkg⟩
  }
  exact ⟨cert, statementUnary, acceptanceUnary, acceptedUnary⟩

end BEDC.Derived.InscribedRouteUp
