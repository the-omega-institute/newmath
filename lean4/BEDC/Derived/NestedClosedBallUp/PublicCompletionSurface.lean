import BEDC.Derived.NestedClosedBallUp.PublicExport

namespace BEDC.Derived.NestedClosedBallUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Unary

theorem NestedClosedBallPublicCompletionSurface
    {M K F S R D E H C P N centerWindow readbackWindow dyadicSeal realSeal packageRead
      publicRead completionRead : BHist} :
    Cont F S centerWindow ->
      Cont centerWindow R readbackWindow ->
        Cont readbackWindow D dyadicSeal ->
          Cont dyadicSeal E realSeal ->
            Cont realSeal P packageRead ->
              Cont packageRead N publicRead ->
                Cont publicRead K completionRead ->
                  UnaryHistory F ->
                    UnaryHistory S ->
                      UnaryHistory R ->
                        UnaryHistory D ->
                          UnaryHistory E ->
                            UnaryHistory P ->
                              UnaryHistory N ->
                                UnaryHistory K ->
                                  SemanticNameCert
                                      (fun row : BHist =>
                                        hsame row completionRead /\ UnaryHistory row)
                                      (fun row : BHist =>
                                        hsame row publicRead \/ hsame row K \/
                                          hsame row completionRead)
                                      (fun row : BHist =>
                                        UnaryHistory row /\
                                          Cont publicRead K completionRead)
                                      hsame /\
                                    UnaryHistory publicRead /\ UnaryHistory completionRead /\
                                      Cont publicRead K completionRead /\
                                        TasteGate.NestedClosedBallTasteGate_single_carrier_alignment_fields
                                            (TasteGate.NestedClosedBallUp.mk M K F S R D E H C
                                              P N) =
                                          [M, K, F, S, R, D, E, H, C, P, N] := by
  -- BEDC touchpoint anchor: BHist Cont hsame SemanticNameCert UnaryHistory
  intro filterStreamRoute centerReadbackRoute readbackDyadicRoute dyadicRealRoute
    realPackageRoute packagePublicRoute publicCompletionRoute filterUnary streamUnary
    readbackUnary dyadicUnary realUnary packageUnary nameUnary serviceUnary
  have exported :=
    NestedClosedBallPublicNameCertExport
      (M := M) (K := K) (F := F) (S := S) (R := R) (D := D) (E := E) (H := H)
      (C := C) (P := P) (N := N) (centerWindow := centerWindow)
      (readbackWindow := readbackWindow) (dyadicSeal := dyadicSeal)
      (realSeal := realSeal) (packageRead := packageRead) (publicRead := publicRead)
      filterStreamRoute centerReadbackRoute readbackDyadicRoute dyadicRealRoute
      realPackageRoute packagePublicRoute filterUnary streamUnary readbackUnary dyadicUnary
      realUnary packageUnary nameUnary
  obtain ⟨_publicCert, publicUnary, fieldsRow⟩ := exported
  have completionUnary : UnaryHistory completionRead :=
    unary_cont_closed publicUnary serviceUnary publicCompletionRoute
  have sourceCompletion : hsame completionRead completionRead /\ UnaryHistory completionRead :=
    ⟨hsame_refl completionRead, completionUnary⟩
  have cert :
      SemanticNameCert
        (fun row : BHist => hsame row completionRead /\ UnaryHistory row)
        (fun row : BHist =>
          hsame row publicRead \/ hsame row K \/ hsame row completionRead)
        (fun row : BHist => UnaryHistory row /\ Cont publicRead K completionRead)
        hsame := {
    core := {
      carrier_inhabited := Exists.intro completionRead sourceCompletion
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
      exact Or.inr (Or.inr source.left)
    ledger_sound := by
      intro _row source
      exact ⟨source.right, publicCompletionRoute⟩
  }
  exact ⟨cert, publicUnary, completionUnary, publicCompletionRoute, fieldsRow⟩

end BEDC.Derived.NestedClosedBallUp
