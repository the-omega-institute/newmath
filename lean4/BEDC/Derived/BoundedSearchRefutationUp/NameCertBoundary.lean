import BEDC.Derived.BoundedSearchRefutationUp

namespace BEDC.Derived.BoundedSearchRefutationUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem BoundedSearchRefutationNameCertBoundary [AskSetup] [PackageSetup]
    {A K F R G H C P N witnessRead gapRead publicRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    BoundedSearchRefutationCarrier A K F R G H C P N bundle pkg ->
      Cont F R witnessRead ->
        Cont F G gapRead ->
          Cont witnessRead gapRead publicRead ->
            PkgSig bundle publicRead pkg ->
              SemanticNameCert
                  (fun row : BHist => hsame row publicRead ∧ UnaryHistory row)
                  (fun row : BHist =>
                    hsame row A ∨ hsame row K ∨ hsame row F ∨ hsame row R ∨
                      hsame row G ∨ hsame row witnessRead ∨ hsame row gapRead ∨
                        hsame row publicRead)
                  (fun row : BHist =>
                    UnaryHistory row ∧ Cont F R witnessRead ∧ Cont F G gapRead ∧
                      Cont witnessRead gapRead publicRead ∧ PkgSig bundle publicRead pkg)
                  hsame ∧
                UnaryHistory witnessRead ∧ UnaryHistory gapRead ∧
                  UnaryHistory publicRead := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig hsame SemanticNameCert UnaryHistory
  intro carrier witnessRoute gapRoute publicRoute publicPkg
  obtain ⟨_aUnary, _kUnary, fUnary, rUnary, gUnary, _hUnary, _nUnary,
    _akFrontier, _frTransport, _hcGap, _provenancePkg, _namePkg⟩ := carrier
  have witnessUnary : UnaryHistory witnessRead :=
    unary_cont_closed fUnary rUnary witnessRoute
  have gapUnary : UnaryHistory gapRead :=
    unary_cont_closed fUnary gUnary gapRoute
  have publicUnary : UnaryHistory publicRead :=
    unary_cont_closed witnessUnary gapUnary publicRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row publicRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row A ∨ hsame row K ∨ hsame row F ∨ hsame row R ∨ hsame row G ∨
              hsame row witnessRead ∨ hsame row gapRead ∨ hsame row publicRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont F R witnessRead ∧ Cont F G gapRead ∧
              Cont witnessRead gapRead publicRead ∧ PkgSig bundle publicRead pkg)
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
      exact Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr
        source.left
    ledger_sound := by
      intro _row source
      exact ⟨source.right, witnessRoute, gapRoute, publicRoute, publicPkg⟩
  }
  exact ⟨cert, witnessUnary, gapUnary, publicUnary⟩

end BEDC.Derived.BoundedSearchRefutationUp
