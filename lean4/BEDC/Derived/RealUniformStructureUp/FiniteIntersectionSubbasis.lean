import BEDC.Derived.RealUniformStructureUp

namespace BEDC.Derived.RealUniformStructureUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem RealUniformStructureFiniteIntersectionSubbasis [AskSetup] [PackageSetup]
    {R M U F D S Q H C P N left right meet meetEntourage : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    RealUniformStructureCarrier R M U F D S Q H C P N bundle pkg ->
      Cont R D left ->
        Cont R D right ->
          Cont left right meet ->
            Cont meet U meetEntourage ->
              PkgSig bundle meetEntourage pkg ->
                SemanticNameCert
                    (fun row : BHist => hsame row meetEntourage ∧ UnaryHistory row)
                    (fun row : BHist =>
                      hsame row R ∨ hsame row D ∨ hsame row U ∨ hsame row left ∨
                        hsame row right ∨ hsame row meet ∨ hsame row meetEntourage)
                    (fun row : BHist =>
                      UnaryHistory row ∧ Cont R D left ∧ Cont R D right ∧
                        Cont left right meet ∧ Cont meet U meetEntourage ∧
                          PkgSig bundle meetEntourage pkg)
                    hsame ∧
                  UnaryHistory left ∧ UnaryHistory right ∧ UnaryHistory meet ∧
                    UnaryHistory meetEntourage := by
  -- BEDC touchpoint anchor: RealUniformStructureCarrier BHist Cont ProbeBundle PkgSig hsame SemanticNameCert UnaryHistory
  intro carrier leftRoute rightRoute meetRoute entourageRoute entouragePkg
  have rUnary : UnaryHistory R := carrier.left
  have uUnary : UnaryHistory U := carrier.right.right.left
  have dUnary : UnaryHistory D := carrier.right.right.right.right.left
  have leftUnary : UnaryHistory left :=
    unary_cont_closed rUnary dUnary leftRoute
  have rightUnary : UnaryHistory right :=
    unary_cont_closed rUnary dUnary rightRoute
  have meetUnary : UnaryHistory meet :=
    unary_cont_closed leftUnary rightUnary meetRoute
  have meetEntourageUnary : UnaryHistory meetEntourage :=
    unary_cont_closed meetUnary uUnary entourageRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row meetEntourage ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row R ∨ hsame row D ∨ hsame row U ∨ hsame row left ∨
              hsame row right ∨ hsame row meet ∨ hsame row meetEntourage)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont R D left ∧ Cont R D right ∧
              Cont left right meet ∧ Cont meet U meetEntourage ∧
                PkgSig bundle meetEntourage pkg)
          hsame := {
    core := {
      carrier_inhabited :=
        Exists.intro meetEntourage ⟨hsame_refl meetEntourage, meetEntourageUnary⟩
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
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr source.left)))))
    ledger_sound := by
      intro _row source
      exact ⟨source.right, leftRoute, rightRoute, meetRoute, entourageRoute, entouragePkg⟩
  }
  exact ⟨cert, leftUnary, rightUnary, meetUnary, meetEntourageUnary⟩

end BEDC.Derived.RealUniformStructureUp
