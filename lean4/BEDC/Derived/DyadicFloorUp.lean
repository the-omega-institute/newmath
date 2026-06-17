import BEDC.Derived.DyadicFloorUp.TasteGate
import BEDC.FKernel.Cont
import BEDC.FKernel.NameCert
import BEDC.FKernel.Unary

namespace BEDC.Derived.DyadicFloorUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Unary

theorem DyadicFloorRegSeqRatHandoff
    {x k d s lower upper modulus regular realSeal H C P N regularWindow dyadicWindow
      sealedWindow : BHist} :
    Cont modulus regular regularWindow ->
      Cont regularWindow d dyadicWindow ->
        Cont dyadicWindow realSeal sealedWindow ->
          UnaryHistory modulus ->
            UnaryHistory regular ->
              UnaryHistory d ->
                UnaryHistory realSeal ->
                  UnaryHistory regularWindow ∧ UnaryHistory dyadicWindow ∧
                    UnaryHistory sealedWindow ∧ Cont modulus regular regularWindow ∧
                      Cont regularWindow d dyadicWindow ∧
                        Cont dyadicWindow realSeal sealedWindow ∧
                          dyadicFloorFields
                              (DyadicFloorUp.mk x k d s lower upper modulus regular realSeal H C P N) =
                            [x, k, d, s, lower, upper, modulus, regular, realSeal, H, C, P, N] := by
  -- BEDC touchpoint anchor: BHist Cont UnaryHistory
  intro modulusRegularRoute regularDyadicRoute dyadicSealRoute modulusUnary regularUnary
    dyadicUnary sealUnary
  have regularWindowUnary : UnaryHistory regularWindow :=
    unary_cont_closed modulusUnary regularUnary modulusRegularRoute
  have dyadicWindowUnary : UnaryHistory dyadicWindow :=
    unary_cont_closed regularWindowUnary dyadicUnary regularDyadicRoute
  have sealedWindowUnary : UnaryHistory sealedWindow :=
    unary_cont_closed dyadicWindowUnary sealUnary dyadicSealRoute
  exact
    ⟨regularWindowUnary, dyadicWindowUnary, sealedWindowUnary, modulusRegularRoute,
      regularDyadicRoute, dyadicSealRoute, rfl⟩

theorem DyadicFloorBoundingInterval
    {x k d s lower upper modulus regular realSeal H C P N lowerRead upperRead
      regularWindow : BHist} :
    Cont d lower lowerRead ->
      Cont s upper upperRead ->
        Cont modulus regular regularWindow ->
          UnaryHistory d ->
            UnaryHistory s ->
              UnaryHistory lower ->
                UnaryHistory upper ->
                  UnaryHistory modulus ->
                    UnaryHistory regular ->
                      dyadicFloorFields
                            (DyadicFloorUp.mk x k d s lower upper modulus regular realSeal H C P N) =
                          [x, k, d, s, lower, upper, modulus, regular, realSeal, H, C, P, N] ∧
                        UnaryHistory lowerRead ∧ UnaryHistory upperRead ∧
                          UnaryHistory regularWindow := by
  -- BEDC touchpoint anchor: BHist Cont UnaryHistory
  intro lowerRoute upperRoute regularRoute dyadicUnary successorUnary lowerUnary upperUnary
    modulusUnary regularUnary
  have lowerReadUnary : UnaryHistory lowerRead :=
    unary_cont_closed dyadicUnary lowerUnary lowerRoute
  have upperReadUnary : UnaryHistory upperRead :=
    unary_cont_closed successorUnary upperUnary upperRoute
  have regularWindowUnary : UnaryHistory regularWindow :=
    unary_cont_closed modulusUnary regularUnary regularRoute
  exact ⟨rfl, lowerReadUnary, upperReadUnary, regularWindowUnary⟩

theorem DyadicFloorCarrier_window_obligations
    {x k d s lower upper modulus regular realSeal H C P N scaleWindow lowerWindow
      upperWindow : BHist} :
    Cont k d scaleWindow ->
      Cont scaleWindow lower lowerWindow ->
        Cont lowerWindow upper upperWindow ->
          UnaryHistory k ->
            UnaryHistory d ->
              UnaryHistory lower ->
                UnaryHistory upper ->
                  UnaryHistory scaleWindow ∧ UnaryHistory lowerWindow ∧
                    UnaryHistory upperWindow ∧ Cont k d scaleWindow ∧
                      Cont scaleWindow lower lowerWindow ∧
                        Cont lowerWindow upper upperWindow ∧
                          dyadicFloorFields
                              (DyadicFloorUp.mk x k d s lower upper modulus regular realSeal H C P N) =
                            [x, k, d, s, lower, upper, modulus, regular, realSeal, H, C, P, N] := by
  -- BEDC touchpoint anchor: BHist Cont UnaryHistory
  intro scaleRoute lowerRoute upperRoute kUnary dUnary lowerUnary upperUnary
  have scaleUnary : UnaryHistory scaleWindow :=
    unary_cont_closed kUnary dUnary scaleRoute
  have lowerWindowUnary : UnaryHistory lowerWindow :=
    unary_cont_closed scaleUnary lowerUnary lowerRoute
  have upperWindowUnary : UnaryHistory upperWindow :=
    unary_cont_closed lowerWindowUnary upperUnary upperRoute
  exact
    ⟨scaleUnary, lowerWindowUnary, upperWindowUnary, scaleRoute, lowerRoute, upperRoute, rfl⟩

theorem DyadicFloorCarrier_real_seal_nonescape
    {x k d s lower upper modulus regular realSeal H C P N regularWindow dyadicWindow
      sealedWindow : BHist} :
    Cont modulus regular regularWindow ->
      Cont regularWindow d dyadicWindow ->
        Cont dyadicWindow realSeal sealedWindow ->
          UnaryHistory modulus ->
            UnaryHistory regular ->
              UnaryHistory d ->
                UnaryHistory realSeal ->
                  SemanticNameCert
                      (fun row : BHist => hsame row sealedWindow ∧ UnaryHistory row)
                      (fun row : BHist =>
                        hsame row sealedWindow ∧ Cont dyadicWindow realSeal sealedWindow)
                      (fun row : BHist =>
                        hsame row sealedWindow ∧
                          dyadicFloorFields
                              (DyadicFloorUp.mk x k d s lower upper modulus regular realSeal H C P N) =
                            [x, k, d, s, lower, upper, modulus, regular, realSeal, H, C, P, N])
                      hsame ∧
                    UnaryHistory sealedWindow ∧ Cont dyadicWindow realSeal sealedWindow := by
  -- BEDC touchpoint anchor: BHist Cont hsame SemanticNameCert UnaryHistory
  intro modulusRegularRoute regularDyadicRoute dyadicSealRoute modulusUnary regularUnary dyadicUnary
    sealUnary
  have regularWindowUnary : UnaryHistory regularWindow :=
    unary_cont_closed modulusUnary regularUnary modulusRegularRoute
  have dyadicWindowUnary : UnaryHistory dyadicWindow :=
    unary_cont_closed regularWindowUnary dyadicUnary regularDyadicRoute
  have sealedWindowUnary : UnaryHistory sealedWindow :=
    unary_cont_closed dyadicWindowUnary sealUnary dyadicSealRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row sealedWindow ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row sealedWindow ∧ Cont dyadicWindow realSeal sealedWindow)
          (fun row : BHist =>
            hsame row sealedWindow ∧
              dyadicFloorFields
                  (DyadicFloorUp.mk x k d s lower upper modulus regular realSeal H C P N) =
                [x, k, d, s, lower, upper, modulus, regular, realSeal, H, C, P, N])
          hsame := by
    exact {
      core := {
        carrier_inhabited :=
          Exists.intro sealedWindow ⟨hsame_refl sealedWindow, sealedWindowUnary⟩
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
        exact ⟨sourceRow.left, dyadicSealRoute⟩
      ledger_sound := by
        intro _row sourceRow
        exact ⟨sourceRow.left, rfl⟩
    }
  exact ⟨cert, sealedWindowUnary, dyadicSealRoute⟩

end BEDC.Derived.DyadicFloorUp
