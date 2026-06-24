import BEDC.Derived.StopCodonZeckendorfSuffixUp.TasteGate
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

theorem StopCodonZeckendorfSuffixScopeGrounding [AskSetup] [PackageSetup]
    {atlas window suffix legality bridge separation boundary transport route provenance name
      atlasRead suffixRead scopedRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    UnaryHistory atlas →
      UnaryHistory window →
        UnaryHistory suffix →
          UnaryHistory legality →
            UnaryHistory bridge →
              UnaryHistory separation →
                UnaryHistory boundary →
                  UnaryHistory transport →
                    UnaryHistory route →
                      UnaryHistory name →
                        Cont atlas window atlasRead →
                          Cont atlasRead suffix suffixRead →
                            Cont suffixRead route scopedRead →
                              PkgSig bundle provenance pkg →
                                PkgSig bundle name pkg →
                                  SemanticNameCert
                                      (fun row : BHist => hsame row scopedRead ∧ UnaryHistory row)
                                      (fun row : BHist =>
                                        hsame row atlas ∨ hsame row window ∨
                                          hsame row suffix ∨ hsame row legality ∨
                                            hsame row bridge ∨ hsame row separation ∨
                                              hsame row boundary ∨ hsame row transport ∨
                                                hsame row route ∨ hsame row provenance ∨
                                                  hsame row name ∨ hsame row scopedRead)
                                      (fun row : BHist =>
                                        UnaryHistory row ∧ Cont atlas window atlasRead ∧
                                          Cont atlasRead suffix suffixRead ∧
                                            Cont suffixRead route scopedRead ∧
                                              PkgSig bundle provenance pkg ∧
                                                PkgSig bundle name pkg)
                                      hsame ∧
                                    UnaryHistory atlasRead ∧ UnaryHistory suffixRead ∧
                                      UnaryHistory scopedRead := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig hsame SemanticNameCert
  intro atlasUnary windowUnary suffixUnary _legalityUnary _bridgeUnary _separationUnary
    _boundaryUnary _transportUnary routeUnary _nameUnary atlasRoute suffixRoute scopedRoute
    provenancePkg namePkg
  have atlasReadUnary : UnaryHistory atlasRead :=
    unary_cont_closed atlasUnary windowUnary atlasRoute
  have suffixReadUnary : UnaryHistory suffixRead :=
    unary_cont_closed atlasReadUnary suffixUnary suffixRoute
  have scopedReadUnary : UnaryHistory scopedRead :=
    unary_cont_closed suffixReadUnary routeUnary scopedRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row scopedRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row atlas ∨ hsame row window ∨ hsame row suffix ∨ hsame row legality ∨
              hsame row bridge ∨ hsame row separation ∨ hsame row boundary ∨
                hsame row transport ∨ hsame row route ∨ hsame row provenance ∨
                  hsame row name ∨ hsame row scopedRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont atlas window atlasRead ∧
              Cont atlasRead suffix suffixRead ∧ Cont suffixRead route scopedRead ∧
                PkgSig bundle provenance pkg ∧ PkgSig bundle name pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro scopedRead ⟨hsame_refl scopedRead, scopedReadUnary⟩
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
      exact
        Or.inr
          (Or.inr
            (Or.inr
              (Or.inr
                (Or.inr
                  (Or.inr
                    (Or.inr
                      (Or.inr (Or.inr (Or.inr (Or.inr source.left))))))))))
    ledger_sound := by
      intro _row source
      exact ⟨source.right, atlasRoute, suffixRoute, scopedRoute, provenancePkg, namePkg⟩
  }
  exact ⟨cert, atlasReadUnary, suffixReadUnary, scopedReadUnary⟩

end BEDC.Derived.StopCodonZeckendorfSuffixUp
