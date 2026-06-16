import BEDC.Derived.DyadicFloorUp.TasteGate
import BEDC.FKernel.Cont
import BEDC.FKernel.Unary

namespace BEDC.Derived.DyadicFloorUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Unary

def DyadicFloorClassifier
    (x k d s lower upper modulus regular realSeal H C P N lowerRead upperRead
      classifierRead : BHist) : Prop :=
  -- BEDC touchpoint anchor: BHist Cont hsame UnaryHistory
  UnaryHistory k ∧ UnaryHistory d ∧ UnaryHistory lower ∧ UnaryHistory upper ∧
    UnaryHistory modulus ∧ UnaryHistory regular ∧ UnaryHistory realSeal ∧ Cont k d s ∧
      Cont d lower lowerRead ∧ Cont s upper upperRead ∧
        Cont modulus regular classifierRead ∧ hsame H (append x k)

theorem DyadicFloorClassifier_window_obligations
    {x k d s lower upper modulus regular realSeal H C P N lowerRead upperRead
      classifierRead : BHist} :
    DyadicFloorClassifier x k d s lower upper modulus regular realSeal H C P N lowerRead
        upperRead classifierRead →
      UnaryHistory s ∧ UnaryHistory lowerRead ∧ UnaryHistory upperRead ∧
        UnaryHistory classifierRead ∧ Cont k d s ∧ Cont d lower lowerRead ∧
          Cont s upper upperRead ∧ Cont modulus regular classifierRead ∧
            dyadicFloorFields
                (DyadicFloorUp.mk x k d s lower upper modulus regular realSeal H C P N) =
              [x, k, d, s, lower, upper, modulus, regular, realSeal, H, C, P, N] := by
  -- BEDC touchpoint anchor: BHist Cont hsame UnaryHistory
  intro h
  exact
    match h with
    | ⟨kUnary, dUnary, lowerUnary, upperUnary, modulusUnary, regularUnary, _realSealUnary,
        successorRoute, lowerRoute, upperRoute, classifierRoute, _transportSame⟩ =>
        let successorUnary : UnaryHistory s :=
          unary_cont_closed kUnary dUnary successorRoute
        let lowerReadUnary : UnaryHistory lowerRead :=
          unary_cont_closed dUnary lowerUnary lowerRoute
        let upperReadUnary : UnaryHistory upperRead :=
          unary_cont_closed successorUnary upperUnary upperRoute
        let classifierReadUnary : UnaryHistory classifierRead :=
          unary_cont_closed modulusUnary regularUnary classifierRoute
        ⟨successorUnary, lowerReadUnary, upperReadUnary, classifierReadUnary, successorRoute,
          lowerRoute, upperRoute, classifierRoute, rfl⟩

end BEDC.Derived.DyadicFloorUp
