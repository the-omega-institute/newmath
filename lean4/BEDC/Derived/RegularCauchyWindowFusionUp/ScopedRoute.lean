import BEDC.Derived.RegularCauchyWindowFusionUp.NameCertObligations

namespace BEDC.Derived.RegularCauchyWindowFusionUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem RegularCauchyWindowFusionScopedRoute [AskSetup] [PackageSetup]
    {R W S D E H C P N seedWindow regularRead dyadicRead modulusRead
      diagonalRead stationaryRead realSeal : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    UnaryHistory R ->
      UnaryHistory W ->
        UnaryHistory S ->
          UnaryHistory D ->
            UnaryHistory E ->
              UnaryHistory H ->
                UnaryHistory C ->
                  UnaryHistory N ->
                    Cont R W seedWindow ->
                      Cont seedWindow S regularRead ->
                        Cont regularRead D dyadicRead ->
                          Cont dyadicRead H modulusRead ->
                            Cont modulusRead C diagonalRead ->
                              Cont diagonalRead N stationaryRead ->
                                Cont stationaryRead E realSeal ->
                                  PkgSig bundle P pkg ->
                                    PkgSig bundle realSeal pkg ->
                                      SemanticNameCert
                                          (fun row : BHist =>
                                            hsame row realSeal ∧ UnaryHistory row)
                                          (fun row : BHist =>
                                            hsame row R ∨ hsame row W ∨
                                              hsame row S ∨ hsame row D ∨
                                                hsame row E ∨ hsame row H ∨
                                                  hsame row C ∨ hsame row P ∨
                                                    hsame row N ∨ hsame row seedWindow ∨
                                                      hsame row regularRead ∨
                                                        hsame row dyadicRead ∨
                                                          hsame row modulusRead ∨
                                                            hsame row diagonalRead ∨
                                                              hsame row stationaryRead ∨
                                                                hsame row realSeal)
                                          (fun row : BHist =>
                                            UnaryHistory row ∧
                                              Cont R W seedWindow ∧
                                                Cont seedWindow S regularRead ∧
                                                  Cont regularRead D dyadicRead ∧
                                                    Cont dyadicRead H modulusRead ∧
                                                      Cont modulusRead C diagonalRead ∧
                                                        Cont diagonalRead N stationaryRead ∧
                                                          Cont stationaryRead E realSeal ∧
                                                            PkgSig bundle realSeal pkg)
                                          hsame ∧
                                        UnaryHistory seedWindow ∧
                                          UnaryHistory regularRead ∧
                                            UnaryHistory dyadicRead ∧
                                              UnaryHistory modulusRead ∧
                                                UnaryHistory diagonalRead ∧
                                                  UnaryHistory stationaryRead ∧
                                                    UnaryHistory realSeal := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig hsame SemanticNameCert
  intro rUnary wUnary sUnary dUnary eUnary hUnary cUnary nUnary seedRoute regularRoute
    dyadicRoute modulusRoute diagonalRoute stationaryRoute sealRoute _pkgP realSealPkg
  have seedUnary : UnaryHistory seedWindow :=
    unary_cont_closed rUnary wUnary seedRoute
  have regularUnary : UnaryHistory regularRead :=
    unary_cont_closed seedUnary sUnary regularRoute
  have dyadicUnary : UnaryHistory dyadicRead :=
    unary_cont_closed regularUnary dUnary dyadicRoute
  have modulusUnary : UnaryHistory modulusRead :=
    unary_cont_closed dyadicUnary hUnary modulusRoute
  have diagonalUnary : UnaryHistory diagonalRead :=
    unary_cont_closed modulusUnary cUnary diagonalRoute
  have stationaryUnary : UnaryHistory stationaryRead :=
    unary_cont_closed diagonalUnary nUnary stationaryRoute
  have realSealUnary : UnaryHistory realSeal :=
    unary_cont_closed stationaryUnary eUnary sealRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row realSeal ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row R ∨ hsame row W ∨ hsame row S ∨ hsame row D ∨
              hsame row E ∨ hsame row H ∨ hsame row C ∨ hsame row P ∨
                hsame row N ∨ hsame row seedWindow ∨ hsame row regularRead ∨
                  hsame row dyadicRead ∨ hsame row modulusRead ∨
                    hsame row diagonalRead ∨ hsame row stationaryRead ∨
                      hsame row realSeal)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont R W seedWindow ∧ Cont seedWindow S regularRead ∧
              Cont regularRead D dyadicRead ∧ Cont dyadicRead H modulusRead ∧
                Cont modulusRead C diagonalRead ∧ Cont diagonalRead N stationaryRead ∧
                  Cont stationaryRead E realSeal ∧ PkgSig bundle realSeal pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro realSeal ⟨hsame_refl realSeal, realSealUnary⟩
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
                      (Or.inr
                        (Or.inr
                          (Or.inr
                            (Or.inr
                              (Or.inr
                                (Or.inr
                                  (Or.inr
                                    (Or.inr source.left))))))))))))))
    ledger_sound := by
      intro _row source
      exact
        ⟨source.right, seedRoute, regularRoute, dyadicRoute, modulusRoute,
          diagonalRoute, stationaryRoute, sealRoute, realSealPkg⟩
  }
  exact
    ⟨cert, seedUnary, regularUnary, dyadicUnary, modulusUnary, diagonalUnary,
      stationaryUnary, realSealUnary⟩

end BEDC.Derived.RegularCauchyWindowFusionUp
