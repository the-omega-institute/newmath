import BEDC.Derived.ModulusContinuityUp.TasteGate

namespace BEDC.Derived.ModulusContinuityUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem ModulusContinuityRealEqualityHandoff [AskSetup] [PackageSetup]
    {graph sourceWindow modulus dyadic readback realSeal equalityBoundary toleranceRead
      windowRead graphRead readbackRead realRead equalityRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    UnaryHistory graph →
      UnaryHistory sourceWindow →
        UnaryHistory modulus →
          UnaryHistory dyadic →
            UnaryHistory readback →
              UnaryHistory realSeal →
                UnaryHistory equalityBoundary →
                  Cont dyadic modulus toleranceRead →
                    Cont toleranceRead sourceWindow windowRead →
                      Cont windowRead graph graphRead →
                        Cont graphRead readback readbackRead →
                          Cont readbackRead realSeal realRead →
                            Cont realRead equalityBoundary equalityRead →
                              PkgSig bundle equalityRead pkg →
                                SemanticNameCert
                                    (fun row : BHist => hsame row equalityRead ∧ UnaryHistory row)
                                    (fun row : BHist =>
                                      hsame row dyadic ∨ hsame row modulus ∨
                                        hsame row sourceWindow ∨ hsame row graph ∨
                                          hsame row readback ∨ hsame row realSeal ∨
                                            hsame row equalityBoundary ∨ hsame row equalityRead)
                                    (fun row : BHist =>
                                      UnaryHistory row ∧ Cont dyadic modulus toleranceRead ∧
                                        Cont toleranceRead sourceWindow windowRead ∧
                                          Cont windowRead graph graphRead ∧
                                            Cont graphRead readback readbackRead ∧
                                              Cont readbackRead realSeal realRead ∧
                                                Cont realRead equalityBoundary equalityRead ∧
                                                  PkgSig bundle equalityRead pkg)
                                    hsame ∧
                                  UnaryHistory equalityRead := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig hsame SemanticNameCert UnaryHistory
  intro graphUnary sourceWindowUnary modulusUnary dyadicUnary readbackUnary realSealUnary
    equalityBoundaryUnary toleranceRoute windowRoute graphRoute readbackRoute realRoute
    equalityRoute equalityPkg
  have toleranceUnary : UnaryHistory toleranceRead :=
    unary_cont_closed dyadicUnary modulusUnary toleranceRoute
  have windowUnary : UnaryHistory windowRead :=
    unary_cont_closed toleranceUnary sourceWindowUnary windowRoute
  have graphReadUnary : UnaryHistory graphRead :=
    unary_cont_closed windowUnary graphUnary graphRoute
  have readbackReadUnary : UnaryHistory readbackRead :=
    unary_cont_closed graphReadUnary readbackUnary readbackRoute
  have realReadUnary : UnaryHistory realRead :=
    unary_cont_closed readbackReadUnary realSealUnary realRoute
  have equalityReadUnary : UnaryHistory equalityRead :=
    unary_cont_closed realReadUnary equalityBoundaryUnary equalityRoute
  have cert :
      SemanticNameCert
        (fun row : BHist => hsame row equalityRead ∧ UnaryHistory row)
        (fun row : BHist =>
          hsame row dyadic ∨ hsame row modulus ∨ hsame row sourceWindow ∨ hsame row graph ∨
            hsame row readback ∨ hsame row realSeal ∨ hsame row equalityBoundary ∨
              hsame row equalityRead)
        (fun row : BHist =>
          UnaryHistory row ∧ Cont dyadic modulus toleranceRead ∧
            Cont toleranceRead sourceWindow windowRead ∧ Cont windowRead graph graphRead ∧
              Cont graphRead readback readbackRead ∧ Cont readbackRead realSeal realRead ∧
                Cont realRead equalityBoundary equalityRead ∧ PkgSig bundle equalityRead pkg)
        hsame := {
    core := {
      carrier_inhabited := Exists.intro equalityRead
        ⟨hsame_refl equalityRead, equalityReadUnary⟩
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
        intro _row _other sameRows sourceRow
        exact
          ⟨hsame_trans (hsame_symm sameRows) sourceRow.left,
            unary_transport sourceRow.right sameRows⟩
    }
    pattern_sound := by
      intro _row sourceRow
      exact Or.inr
        (Or.inr
          (Or.inr
            (Or.inr
              (Or.inr
                (Or.inr
                  (Or.inr sourceRow.left))))))
    ledger_sound := by
      intro _row sourceRow
      exact
        ⟨sourceRow.right, toleranceRoute, windowRoute, graphRoute, readbackRoute, realRoute,
          equalityRoute, equalityPkg⟩
  }
  exact ⟨cert, equalityReadUnary⟩

end BEDC.Derived.ModulusContinuityUp
