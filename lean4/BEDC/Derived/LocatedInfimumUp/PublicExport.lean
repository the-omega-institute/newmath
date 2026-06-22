import BEDC.Derived.LocatedInfimumUp
import BEDC.FKernel.NameCert

namespace BEDC.Derived.LocatedInfimumUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem LocatedInfimumPublicExport [AskSetup] [PackageSetup]
    {family lower greatest window regseq realSeal transport route provenance name
      publicRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    LocatedInfimumCarrier family lower greatest window regseq realSeal transport route provenance
        name bundle pkg ->
      Cont lower greatest publicRead ->
        PkgSig bundle publicRead pkg ->
          SemanticNameCert
              (fun row : BHist => hsame row publicRead ∧ UnaryHistory row)
              (fun row : BHist =>
                hsame row family ∨ hsame row lower ∨ hsame row greatest ∨
                  hsame row window ∨ hsame row regseq ∨ hsame row realSeal ∨
                    hsame row publicRead)
              (fun row : BHist =>
                UnaryHistory row ∧ Cont lower greatest publicRead ∧
                  PkgSig bundle publicRead pkg)
              hsame ∧
            UnaryHistory publicRead := by
  -- BEDC touchpoint anchor: LocatedInfimumCarrier BHist Cont ProbeBundle PkgSig SemanticNameCert hsame UnaryHistory
  intro carrier lowerGreatest publicPkg
  obtain ⟨_familyUnary, lowerUnary, greatestUnary, _windowUnary, _regseqUnary,
    _realSealUnary, _transportUnary, _routeUnary, _provenanceUnary, _nameUnary,
    _regseqRealSealRoute, _provenancePkg, _namePkg⟩ := carrier
  have publicUnary : UnaryHistory publicRead :=
    unary_cont_closed lowerUnary greatestUnary lowerGreatest
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row publicRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row family ∨ hsame row lower ∨ hsame row greatest ∨ hsame row window ∨
              hsame row regseq ∨ hsame row realSeal ∨ hsame row publicRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont lower greatest publicRead ∧
              PkgSig bundle publicRead pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro publicRead ⟨hsame_refl publicRead, publicUnary⟩
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
      exact Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr source.left
    ledger_sound := by
      intro _row source
      exact ⟨source.right, lowerGreatest, publicPkg⟩
  }
  exact ⟨cert, publicUnary⟩

end BEDC.Derived.LocatedInfimumUp
