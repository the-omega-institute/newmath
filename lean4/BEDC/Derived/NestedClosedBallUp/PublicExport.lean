import BEDC.Derived.NestedClosedBallUp.ObligationPackage

namespace BEDC.Derived.NestedClosedBallUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Unary

theorem NestedClosedBallPublicNameCertExport
    {M K F S R D E H C P N centerWindow readbackWindow dyadicSeal realSeal packageRead
      publicRead : BHist} :
    Cont F S centerWindow ->
      Cont centerWindow R readbackWindow ->
        Cont readbackWindow D dyadicSeal ->
          Cont dyadicSeal E realSeal ->
            Cont realSeal P packageRead ->
              Cont packageRead N publicRead ->
                UnaryHistory F ->
                  UnaryHistory S ->
                    UnaryHistory R ->
                      UnaryHistory D ->
                        UnaryHistory E ->
                          UnaryHistory P ->
                            UnaryHistory N ->
                              SemanticNameCert
                                  (fun row : BHist => hsame row publicRead ∧ UnaryHistory row)
                                  (fun row : BHist =>
                                    hsame row F ∨ hsame row S ∨ hsame row R ∨ hsame row D ∨
                                      hsame row E ∨ hsame row P ∨ hsame row N ∨
                                        hsame row publicRead)
                                  (fun row : BHist =>
                                    UnaryHistory row ∧ Cont F S centerWindow ∧
                                      Cont centerWindow R readbackWindow ∧
                                        Cont readbackWindow D dyadicSeal ∧
                                          Cont dyadicSeal E realSeal ∧
                                            Cont realSeal P packageRead ∧
                                              Cont packageRead N publicRead)
                                  hsame ∧ UnaryHistory publicRead ∧
                                TasteGate.NestedClosedBallTasteGate_single_carrier_alignment_fields
                                    (TasteGate.NestedClosedBallUp.mk M K F S R D E H C P N) =
                                  [M, K, F, S, R, D, E, H, C, P, N] := by
  -- BEDC touchpoint anchor: BHist Cont hsame SemanticNameCert UnaryHistory
  intro filterStreamRoute centerReadbackRoute readbackDyadicRoute dyadicRealRoute
    realPackageRoute packagePublicRoute filterUnary streamUnary readbackUnary dyadicUnary
    realUnary packageUnary nameUnary
  have centerWindowUnary : UnaryHistory centerWindow :=
    unary_cont_closed filterUnary streamUnary filterStreamRoute
  have readbackWindowUnary : UnaryHistory readbackWindow :=
    unary_cont_closed centerWindowUnary readbackUnary centerReadbackRoute
  have dyadicSealUnary : UnaryHistory dyadicSeal :=
    unary_cont_closed readbackWindowUnary dyadicUnary readbackDyadicRoute
  have realSealUnary : UnaryHistory realSeal :=
    unary_cont_closed dyadicSealUnary realUnary dyadicRealRoute
  have packageReadUnary : UnaryHistory packageRead :=
    unary_cont_closed realSealUnary packageUnary realPackageRoute
  have publicReadUnary : UnaryHistory publicRead :=
    unary_cont_closed packageReadUnary nameUnary packagePublicRoute
  have sourcePublic : hsame publicRead publicRead ∧ UnaryHistory publicRead :=
    ⟨hsame_refl publicRead, publicReadUnary⟩
  have cert :
      SemanticNameCert
        (fun row : BHist => hsame row publicRead ∧ UnaryHistory row)
        (fun row : BHist =>
          hsame row F ∨ hsame row S ∨ hsame row R ∨ hsame row D ∨ hsame row E ∨
            hsame row P ∨ hsame row N ∨ hsame row publicRead)
        (fun row : BHist =>
          UnaryHistory row ∧ Cont F S centerWindow ∧
            Cont centerWindow R readbackWindow ∧ Cont readbackWindow D dyadicSeal ∧
              Cont dyadicSeal E realSeal ∧ Cont realSeal P packageRead ∧
                Cont packageRead N publicRead)
        hsame := {
    core := {
      carrier_inhabited := Exists.intro publicRead sourcePublic
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
        intro row other sameRows source
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
                    (Or.inr source.left))))))
    ledger_sound := by
      intro _row source
      exact
        ⟨source.right, filterStreamRoute, centerReadbackRoute, readbackDyadicRoute,
          dyadicRealRoute, realPackageRoute, packagePublicRoute⟩
  }
  exact ⟨cert, publicReadUnary, rfl⟩

end BEDC.Derived.NestedClosedBallUp
