import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.StopCodonZeckendorfSuffixUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem StopCodonZeckendorfSuffixBridgeBoundary [AskSetup] [PackageSetup]
    {atlas window suffix legality bridge separation boundary transport route provenance
      localName atlasRead suffixRead legalityRead bridgeRead boundaryRead namedRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    UnaryHistory atlas →
      UnaryHistory window →
        UnaryHistory suffix →
          UnaryHistory legality →
            UnaryHistory bridge →
              UnaryHistory boundary →
                UnaryHistory localName →
                  Cont atlas window atlasRead →
                    Cont atlasRead suffix suffixRead →
                      Cont suffixRead legality legalityRead →
                        Cont legalityRead bridge bridgeRead →
                          Cont bridgeRead boundary boundaryRead →
                            Cont boundaryRead localName namedRead →
                              PkgSig bundle provenance pkg →
                                PkgSig bundle namedRead pkg →
                                  SemanticNameCert
                                      (fun row : BHist => hsame row namedRead ∧ UnaryHistory row)
                                      (fun row : BHist =>
                                        hsame row atlas ∨ hsame row window ∨
                                          hsame row suffix ∨ hsame row legality ∨
                                            hsame row bridge ∨ hsame row separation ∨
                                              hsame row boundary ∨ hsame row namedRead)
                                      (fun row : BHist =>
                                        UnaryHistory row ∧ Cont atlas window atlasRead ∧
                                          Cont atlasRead suffix suffixRead ∧
                                            Cont suffixRead legality legalityRead ∧
                                              Cont legalityRead bridge bridgeRead ∧
                                                Cont bridgeRead boundary boundaryRead ∧
                                                  Cont boundaryRead localName namedRead ∧
                                                    PkgSig bundle provenance pkg ∧
                                                      PkgSig bundle namedRead pkg)
                                      hsame ∧
                                    UnaryHistory atlasRead ∧ UnaryHistory suffixRead ∧
                                      UnaryHistory legalityRead ∧ UnaryHistory bridgeRead ∧
                                        UnaryHistory boundaryRead ∧ UnaryHistory namedRead := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig hsame SemanticNameCert
  intro atlasUnary windowUnary suffixUnary legalityUnary bridgeUnary boundaryUnary
    localNameUnary atlasRoute suffixRoute legalityRoute bridgeRoute boundaryRoute
    namedRoute provenancePkg namedPkg
  have atlasReadUnary : UnaryHistory atlasRead :=
    unary_cont_closed atlasUnary windowUnary atlasRoute
  have suffixReadUnary : UnaryHistory suffixRead :=
    unary_cont_closed atlasReadUnary suffixUnary suffixRoute
  have legalityReadUnary : UnaryHistory legalityRead :=
    unary_cont_closed suffixReadUnary legalityUnary legalityRoute
  have bridgeReadUnary : UnaryHistory bridgeRead :=
    unary_cont_closed legalityReadUnary bridgeUnary bridgeRoute
  have boundaryReadUnary : UnaryHistory boundaryRead :=
    unary_cont_closed bridgeReadUnary boundaryUnary boundaryRoute
  have namedReadUnary : UnaryHistory namedRead :=
    unary_cont_closed boundaryReadUnary localNameUnary namedRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row namedRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row atlas ∨ hsame row window ∨ hsame row suffix ∨ hsame row legality ∨
              hsame row bridge ∨ hsame row separation ∨ hsame row boundary ∨
                hsame row namedRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont atlas window atlasRead ∧
              Cont atlasRead suffix suffixRead ∧ Cont suffixRead legality legalityRead ∧
                Cont legalityRead bridge bridgeRead ∧ Cont bridgeRead boundary boundaryRead ∧
                  Cont boundaryRead localName namedRead ∧ PkgSig bundle provenance pkg ∧
                    PkgSig bundle namedRead pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro namedRead ⟨hsame_refl namedRead, namedReadUnary⟩
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
        ⟨source.right, atlasRoute, suffixRoute, legalityRoute, bridgeRoute, boundaryRoute,
          namedRoute, provenancePkg, namedPkg⟩
  }
  exact
    ⟨cert, atlasReadUnary, suffixReadUnary, legalityReadUnary, bridgeReadUnary,
      boundaryReadUnary, namedReadUnary⟩

end BEDC.Derived.StopCodonZeckendorfSuffixUp
