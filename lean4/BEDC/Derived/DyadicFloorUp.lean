import BEDC.Derived.DyadicFloorUp.TasteGate
import BEDC.FKernel.Cont
import BEDC.FKernel.Unary

namespace BEDC.Derived.DyadicFloorUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
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

end BEDC.Derived.DyadicFloorUp
