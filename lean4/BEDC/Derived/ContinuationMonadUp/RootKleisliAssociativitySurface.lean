import BEDC.Derived.ContinuationMonadUp

namespace BEDC.Derived.ContinuationMonadUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem ContinuationMonadBHistBindAssociativityInduction [AskSetup] [PackageSetup]
    {A B C f g u H K L N step left right reassoc named : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    UnaryHistory A ->
      UnaryHistory B ->
        UnaryHistory C ->
          UnaryHistory f ->
            UnaryHistory g ->
              UnaryHistory u ->
                UnaryHistory H ->
                  UnaryHistory K ->
                    UnaryHistory L ->
                      UnaryHistory N ->
                        Cont A f left ->
                          Cont left g right ->
                            Cont B g step ->
                              Cont A step reassoc ->
                                Cont right H named ->
                                  PkgSig bundle L pkg ->
                                    hsame right reassoc ->
                                      SemanticNameCert
                                          (fun row : BHist =>
                                            hsame row named ∧ UnaryHistory row)
                                          (fun row : BHist =>
                                            hsame row A ∨ hsame row B ∨ hsame row C ∨
                                              hsame row f ∨ hsame row g ∨ hsame row u ∨
                                                hsame row right ∨ hsame row reassoc ∨
                                                  hsame row named)
                                          (fun row : BHist =>
                                            UnaryHistory row ∧ Cont A f left ∧
                                              Cont left g right ∧ Cont A step reassoc ∧
                                                PkgSig bundle L pkg)
                                          hsame ∧
                                        UnaryHistory named := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig hsame SemanticNameCert UnaryHistory
  intro rowsA rowsB _rowsC rowsF rowsG _rowsU rowsH _rowsK _rowsL _rowsN
    leftRoute rightRoute stepRoute reassocRoute namedRoute packageRead sameAssoc
  have leftUnary : UnaryHistory left :=
    unary_cont_closed rowsA rowsF leftRoute
  have rightUnary : UnaryHistory right :=
    unary_cont_closed leftUnary rowsG rightRoute
  have stepUnary : UnaryHistory step :=
    unary_cont_closed rowsB rowsG stepRoute
  have _reassocUnary : UnaryHistory reassoc :=
    unary_cont_closed rowsA stepUnary reassocRoute
  have _reassocUnaryByTransport : UnaryHistory reassoc :=
    unary_transport rightUnary sameAssoc
  have namedUnary : UnaryHistory named :=
    unary_cont_closed rightUnary rowsH namedRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row named ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row A ∨ hsame row B ∨ hsame row C ∨ hsame row f ∨ hsame row g ∨
              hsame row u ∨ hsame row right ∨ hsame row reassoc ∨ hsame row named)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont A f left ∧ Cont left g right ∧
              Cont A step reassoc ∧ PkgSig bundle L pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro named ⟨hsame_refl named, namedUnary⟩
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
      exact Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <|
        Or.inr <| Or.inr source.left
    ledger_sound := by
      intro _row source
      exact ⟨source.right, leftRoute, rightRoute, reassocRoute, packageRead⟩
  }
  exact ⟨cert, namedUnary⟩

end BEDC.Derived.ContinuationMonadUp
