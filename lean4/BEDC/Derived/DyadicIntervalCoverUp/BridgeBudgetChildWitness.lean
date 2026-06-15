import BEDC.Derived.DyadicIntervalCoverUp.RootWindowCoverage

namespace BEDC.Derived.DyadicIntervalCoverUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem DyadicIntervalCoverBridgeBudgetChildWitness [AskSetup] [PackageSetup]
    {lower upper mesh radius member window readback realSeal transport replay provenance
      cert bridgeRead childWitness : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    DyadicIntervalCoverRootObligationSurface lower upper mesh radius member window readback
        realSeal transport replay provenance cert bundle pkg →
      Cont lower upper mesh →
        Cont mesh radius member →
          Cont window readback bridgeRead →
            Cont bridgeRead realSeal childWitness →
              PkgSig bundle childWitness pkg →
                SemanticNameCert
                    (fun row : BHist => hsame row childWitness ∧ UnaryHistory row)
                    (fun row : BHist =>
                      hsame row lower ∨ hsame row upper ∨ hsame row mesh ∨
                        hsame row member ∨ hsame row bridgeRead ∨ hsame row childWitness)
                    (fun row : BHist =>
                      UnaryHistory row ∧ Cont window readback bridgeRead ∧
                        Cont bridgeRead realSeal childWitness ∧ PkgSig bundle childWitness pkg)
                    hsame ∧
                  UnaryHistory childWitness ∧ PkgSig bundle provenance pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame SemanticNameCert UnaryHistory
  intro surface _endpointRoute memberRoute bridgeRoute childRoute childPkg
  have meshUnary : UnaryHistory mesh := surface.right.right.left
  have radiusUnary : UnaryHistory radius := surface.right.right.right.left
  have windowUnary : UnaryHistory window := surface.right.right.right.right.right.left
  have readbackUnary : UnaryHistory readback :=
    surface.right.right.right.right.right.right.left
  have realSealUnary : UnaryHistory realSeal :=
    surface.right.right.right.right.right.right.right.left
  have provenancePkg : PkgSig bundle provenance pkg :=
    surface.right.right.right.right.right.right.right.right.right.right.right.right.left
  have memberUnary : UnaryHistory member :=
    unary_cont_closed meshUnary radiusUnary memberRoute
  have bridgeUnary : UnaryHistory bridgeRead :=
    unary_cont_closed windowUnary readbackUnary bridgeRoute
  have childUnary : UnaryHistory childWitness :=
    unary_cont_closed bridgeUnary realSealUnary childRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row childWitness ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row lower ∨ hsame row upper ∨ hsame row mesh ∨ hsame row member ∨
              hsame row bridgeRead ∨ hsame row childWitness)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont window readback bridgeRead ∧
              Cont bridgeRead realSeal childWitness ∧ PkgSig bundle childWitness pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro childWitness ⟨hsame_refl childWitness, childUnary⟩
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
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr source.left))))
    ledger_sound := by
      intro _row source
      exact ⟨source.right, bridgeRoute, childRoute, childPkg⟩
  }
  exact ⟨cert, childUnary, provenancePkg⟩

end BEDC.Derived.DyadicIntervalCoverUp
