import BEDC.MetaCIC.TypedExamples.ChurchGallery
import BEDC.MetaCIC.TypedExamples.ChurchNatRec
import BEDC.MetaCIC.Beta
import BEDC.MetaCIC.Decidable.CheckClosed
import BEDC.MetaCIC.Decidable.NormalEqDecide

namespace BEDC.MetaCIC

def leibniz_eq : Term :=
  Term.lam Term.sort
    (Term.lam (Term.var 0)
      (Term.lam (Term.var 1)
        (Term.pi (Term.pi (Term.var 2) Term.sort)
          (Term.pi (Term.app (Term.var 0) (Term.var 2))
            (Term.app (Term.var 1) (Term.var 2))))))

def leibniz_refl : Term :=
  Term.lam Term.sort
    (Term.lam (Term.var 0)
      (Term.lam (Term.pi (Term.var 1) Term.sort)
        (Term.lam (Term.app (Term.var 0) (Term.var 1))
          (Term.var 0))))

abbrev leibniz_eq_type_tm : Term :=
  Term.pi Term.sort
    (Term.pi (Term.var 0)
      (Term.pi (Term.var 1) Term.sort))

abbrev leibniz_refl_principal_type_tm : Term :=
  Term.pi Term.sort
    (Term.pi (Term.var 0)
      (Term.pi (Term.pi (Term.var 1) Term.sort)
        (Term.pi (Term.app (Term.var 0) (Term.var 1))
          (Term.app (Term.var 1) (Term.var 2)))))

abbrev leibniz_refl_surface_type_tm : Term :=
  Term.pi Term.sort
    (Term.pi (Term.var 0)
      (Term.app
        (Term.app
          (Term.app leibniz_eq (Term.var 1))
          (Term.var 0))
        (Term.var 0)))

abbrev leibnizEqAt (A x y : Term) : Term :=
  Term.app (Term.app (Term.app leibniz_eq A) x) y

abbrev leibnizEqNormalAt (A x y : Term) : Term :=
  Term.pi (Term.pi A Term.sort)
    (Term.pi (Term.app (Term.var 0) x)
      (Term.app (Term.var 1) y))

abbrev leibnizReflAt (A x : Term) : Term :=
  Term.app (Term.app leibniz_refl A) x

abbrev churchNatZeroEq : Term :=
  leibnizEqAt churchNatTy churchZeroTm churchZeroTm

abbrev churchNatZeroEqNormal : Term :=
  leibnizEqNormalAt churchNatTy churchZeroTm churchZeroTm

abbrev churchNatZeroRefl : Term :=
  leibnizReflAt churchNatTy churchZeroTm

abbrev churchNatOneEq : Term :=
  leibnizEqAt churchNatTy churchOneTm churchOneTm

abbrev churchNatOneEqNormal : Term :=
  leibnizEqNormalAt churchNatTy churchOneTm churchOneTm

abbrev churchNatZeroOneEq : Term :=
  leibnizEqAt churchNatTy churchZeroTm churchOneTm

abbrev churchNatZeroOneEqNormal : Term :=
  leibnizEqNormalAt churchNatTy churchZeroTm churchOneTm

abbrev churchBoolTrueEq : Term :=
  leibnizEqAt churchBoolTy churchTrueTm churchTrueTm

abbrev churchBoolTrueEqNormal : Term :=
  leibnizEqNormalAt churchBoolTy churchTrueTm churchTrueTm

abbrev churchBoolFalseEq : Term :=
  leibnizEqAt churchBoolTy churchFalseTm churchFalseTm

abbrev churchBoolFalseEqNormal : Term :=
  leibnizEqNormalAt churchBoolTy churchFalseTm churchFalseTm

abbrev churchBoolTrueFalseEq : Term :=
  leibnizEqAt churchBoolTy churchTrueTm churchFalseTm

abbrev churchBoolTrueFalseEqNormal : Term :=
  leibnizEqNormalAt churchBoolTy churchTrueTm churchFalseTm

abbrev churchBoolTrueRefl : Term :=
  leibnizReflAt churchBoolTy churchTrueTm

abbrev churchBoolFalseRefl : Term :=
  leibnizReflAt churchBoolTy churchFalseTm

theorem leibniz_eq_type :
    HasType [] leibniz_eq leibniz_eq_type_tm := by
  exact inferTypeCtx_sound [] leibniz_eq leibniz_eq_type_tm rfl

theorem leibniz_eq_type_is_type :
    HasType [] leibniz_eq_type_tm Term.sort := by
  exact inferTypeCtx_sound [] leibniz_eq_type_tm Term.sort rfl

theorem leibniz_refl_type :
    HasType [] leibniz_refl leibniz_refl_principal_type_tm := by
  exact inferTypeCtx_sound [] leibniz_refl leibniz_refl_principal_type_tm rfl

theorem leibniz_refl_principal_type_is_type :
    HasType [] leibniz_refl_principal_type_tm Term.sort := by
  exact inferTypeCtx_sound [] leibniz_refl_principal_type_tm Term.sort rfl

theorem leibniz_refl_surface_type_is_type :
    HasType [] leibniz_refl_surface_type_tm Term.sort := by
  exact inferTypeCtx_sound [] leibniz_refl_surface_type_tm Term.sort rfl

theorem leibniz_refl_surface_type_decides :
    decideClosedBetaConv 6
      leibniz_refl_surface_type_tm
      leibniz_refl_principal_type_tm = true := by
  rfl

theorem church_equality_ctx_lookup_length_lt {Γ : Ctx} {i : Idx} {A : Term}
    (h : Γ.lookup i = some A) :
    i < Γ.length := by
  induction Γ generalizing i A with
  | nil =>
      cases i with
      | zero =>
          cases h
      | succ i =>
          cases h
  | cons T Γ ih =>
      cases i with
      | zero =>
          exact Nat.zero_lt_succ Γ.length
      | succ i =>
          unfold Ctx.lookup at h
          cases hlookup : Ctx.lookup Γ i with
          | none =>
              rw [hlookup] at h
              cases h
          | some B =>
              exact Nat.succ_lt_succ (ih hlookup)

theorem church_equality_hasType_closed_at_context_length
    {Γ : Ctx} {t A : Term}
    (h : HasType Γ t A) :
    ClosedAt Γ.length t := by
  induction h with
  | sortRule Γ =>
      exact ClosedAt.sortClosed
  | varRule Γ i A hlookup =>
      exact ClosedAt.varClosed
        (church_equality_ctx_lookup_length_lt hlookup)
  | piRule Γ dom cod hdom hcod ihdom ihcod =>
      apply ClosedAt.piClosed
      · exact ihdom
      · change ClosedAt (((shift 0 1 dom) :: Γ).length) cod
        exact ihcod
  | lamRule Γ dom body cod hdom hbody ihdom ihbody =>
      apply ClosedAt.lamClosed
      · exact ihdom
      · change ClosedAt (((shift 0 1 dom) :: Γ).length) body
        exact ihbody
  | appRule Γ f a dom cod hf ha ihf iha =>
      exact ClosedAt.appClosed ihf iha

theorem leibniz_eq_closed :
    ClosedAt 0 leibniz_eq := by
  exact church_equality_hasType_closed_at_context_length leibniz_eq_type

theorem leibniz_refl_closed :
    ClosedAt 0 leibniz_refl := by
  exact church_equality_hasType_closed_at_context_length
    leibniz_refl_type

theorem leibniz_eq_type_closed :
    ClosedAt 0 leibniz_eq_type_tm := by
  exact church_equality_hasType_closed_at_context_length
    leibniz_eq_type_is_type

theorem leibniz_refl_principal_type_closed :
    ClosedAt 0 leibniz_refl_principal_type_tm := by
  exact church_equality_hasType_closed_at_context_length
    leibniz_refl_principal_type_is_type

theorem leibniz_refl_surface_type_closed :
    ClosedAt 0 leibniz_refl_surface_type_tm := by
  exact church_equality_hasType_closed_at_context_length
    leibniz_refl_surface_type_is_type

theorem leibnizEqAt_closed {A x y : Term}
    (hA : ClosedAt 0 A) (hx : ClosedAt 0 x) (hy : ClosedAt 0 y) :
    ClosedAt 0 (leibnizEqAt A x y) := by
  exact ClosedAt.appClosed
    (ClosedAt.appClosed
      (ClosedAt.appClosed leibniz_eq_closed hA)
      hx)
    hy

theorem leibnizEqNormalAt_closed {A x y : Term}
    (hA : ClosedAt 0 A) (hx : ClosedAt 0 x) (hy : ClosedAt 0 y) :
    ClosedAt 0 (leibnizEqNormalAt A x y) := by
  unfold leibnizEqNormalAt
  apply ClosedAt.piClosed
  · apply ClosedAt.piClosed
    · exact hA
    · exact ClosedAt.sortClosed
  · apply ClosedAt.piClosed
    · exact ClosedAt.appClosed
        (ClosedAt.varClosed (Nat.zero_lt_succ 0))
        (closedAt_succ 0 x hx)
    · exact ClosedAt.appClosed
        (ClosedAt.varClosed (Nat.lt_succ_self 1))
        (closedAt_succ 1 y (closedAt_succ 0 y hy))

theorem leibnizReflAt_closed {A x : Term}
    (hA : ClosedAt 0 A) (hx : ClosedAt 0 x) :
    ClosedAt 0 (leibnizReflAt A x) := by
  exact ClosedAt.appClosed
    (ClosedAt.appClosed leibniz_refl_closed hA)
    hx

theorem church_bool_ty_closed_local :
    ClosedAt 0 churchBoolTy := by
  exact church_equality_hasType_closed_at_context_length church_bool_type

theorem church_true_closed_local :
    ClosedAt 0 churchTrueTm := by
  exact church_equality_hasType_closed_at_context_length church_true

theorem church_false_closed_local :
    ClosedAt 0 churchFalseTm := by
  exact church_equality_hasType_closed_at_context_length church_false

theorem church_one_closed_local :
    ClosedAt 0 churchOneTm := by
  exact church_equality_hasType_closed_at_context_length church_one

theorem church_nat_zero_eq_closed :
    ClosedAt 0 churchNatZeroEq := by
  exact leibnizEqAt_closed
    ChurchNatRec.church_nat_closed
    ChurchNatRec.church_zero_closed
    ChurchNatRec.church_zero_closed

theorem church_nat_zero_eq_normal_closed :
    ClosedAt 0 churchNatZeroEqNormal := by
  exact leibnizEqNormalAt_closed
    ChurchNatRec.church_nat_closed
    ChurchNatRec.church_zero_closed
    ChurchNatRec.church_zero_closed

theorem church_nat_zero_refl_closed :
    ClosedAt 0 churchNatZeroRefl := by
  exact leibnizReflAt_closed
    ChurchNatRec.church_nat_closed
    ChurchNatRec.church_zero_closed

theorem church_nat_one_eq_closed :
    ClosedAt 0 churchNatOneEq := by
  exact leibnizEqAt_closed
    ChurchNatRec.church_nat_closed
    church_one_closed_local
    church_one_closed_local

theorem church_nat_one_eq_normal_closed :
    ClosedAt 0 churchNatOneEqNormal := by
  exact leibnizEqNormalAt_closed
    ChurchNatRec.church_nat_closed
    church_one_closed_local
    church_one_closed_local

theorem church_nat_zero_one_eq_closed :
    ClosedAt 0 churchNatZeroOneEq := by
  exact leibnizEqAt_closed
    ChurchNatRec.church_nat_closed
    ChurchNatRec.church_zero_closed
    church_one_closed_local

theorem church_nat_zero_one_eq_normal_closed :
    ClosedAt 0 churchNatZeroOneEqNormal := by
  exact leibnizEqNormalAt_closed
    ChurchNatRec.church_nat_closed
    ChurchNatRec.church_zero_closed
    church_one_closed_local

theorem church_bool_true_eq_closed :
    ClosedAt 0 churchBoolTrueEq := by
  exact leibnizEqAt_closed
    church_bool_ty_closed_local
    church_true_closed_local
    church_true_closed_local

theorem church_bool_true_eq_normal_closed :
    ClosedAt 0 churchBoolTrueEqNormal := by
  exact leibnizEqNormalAt_closed
    church_bool_ty_closed_local
    church_true_closed_local
    church_true_closed_local

theorem church_bool_false_eq_closed :
    ClosedAt 0 churchBoolFalseEq := by
  exact leibnizEqAt_closed
    church_bool_ty_closed_local
    church_false_closed_local
    church_false_closed_local

theorem church_bool_false_eq_normal_closed :
    ClosedAt 0 churchBoolFalseEqNormal := by
  exact leibnizEqNormalAt_closed
    church_bool_ty_closed_local
    church_false_closed_local
    church_false_closed_local

theorem church_bool_true_false_eq_closed :
    ClosedAt 0 churchBoolTrueFalseEq := by
  exact leibnizEqAt_closed
    church_bool_ty_closed_local
    church_true_closed_local
    church_false_closed_local

theorem church_bool_true_false_eq_normal_closed :
    ClosedAt 0 churchBoolTrueFalseEqNormal := by
  exact leibnizEqNormalAt_closed
    church_bool_ty_closed_local
    church_true_closed_local
    church_false_closed_local

theorem church_bool_true_refl_closed :
    ClosedAt 0 churchBoolTrueRefl := by
  exact leibnizReflAt_closed
    church_bool_ty_closed_local
    church_true_closed_local

theorem church_bool_false_refl_closed :
    ClosedAt 0 churchBoolFalseRefl := by
  exact leibnizReflAt_closed
    church_bool_ty_closed_local
    church_false_closed_local

theorem church_nat_zero_eq_type :
    HasType [] churchNatZeroEq Term.sort := by
  exact inferTypeCtx_sound [] churchNatZeroEq Term.sort rfl

theorem church_nat_zero_eq_normal_type :
    HasType [] churchNatZeroEqNormal Term.sort := by
  exact inferTypeCtx_sound [] churchNatZeroEqNormal Term.sort rfl

theorem church_nat_one_eq_type :
    HasType [] churchNatOneEq Term.sort := by
  exact inferTypeCtx_sound [] churchNatOneEq Term.sort rfl

theorem church_nat_one_eq_normal_type :
    HasType [] churchNatOneEqNormal Term.sort := by
  exact inferTypeCtx_sound [] churchNatOneEqNormal Term.sort rfl

theorem church_nat_zero_one_eq_type :
    HasType [] churchNatZeroOneEq Term.sort := by
  exact inferTypeCtx_sound [] churchNatZeroOneEq Term.sort rfl

theorem church_nat_zero_one_eq_normal_type :
    HasType [] churchNatZeroOneEqNormal Term.sort := by
  exact inferTypeCtx_sound [] churchNatZeroOneEqNormal Term.sort rfl

theorem church_bool_true_eq_type :
    HasType [] churchBoolTrueEq Term.sort := by
  exact inferTypeCtx_sound [] churchBoolTrueEq Term.sort rfl

theorem church_bool_true_eq_normal_type :
    HasType [] churchBoolTrueEqNormal Term.sort := by
  exact inferTypeCtx_sound [] churchBoolTrueEqNormal Term.sort rfl

theorem church_bool_false_eq_type :
    HasType [] churchBoolFalseEq Term.sort := by
  exact inferTypeCtx_sound [] churchBoolFalseEq Term.sort rfl

theorem church_bool_false_eq_normal_type :
    HasType [] churchBoolFalseEqNormal Term.sort := by
  exact inferTypeCtx_sound [] churchBoolFalseEqNormal Term.sort rfl

theorem church_bool_true_false_eq_type :
    HasType [] churchBoolTrueFalseEq Term.sort := by
  exact inferTypeCtx_sound [] churchBoolTrueFalseEq Term.sort rfl

theorem church_bool_true_false_eq_normal_type :
    HasType [] churchBoolTrueFalseEqNormal Term.sort := by
  exact inferTypeCtx_sound [] churchBoolTrueFalseEqNormal Term.sort rfl

theorem refl_zero_proof :
    HasType [] churchNatZeroRefl churchNatZeroEqNormal := by
  exact inferTypeCtx_sound [] churchNatZeroRefl churchNatZeroEqNormal rfl

theorem refl_true_proof :
    HasType [] churchBoolTrueRefl churchBoolTrueEqNormal := by
  exact inferTypeCtx_sound [] churchBoolTrueRefl churchBoolTrueEqNormal rfl

theorem refl_false_proof :
    HasType [] churchBoolFalseRefl churchBoolFalseEqNormal := by
  exact inferTypeCtx_sound [] churchBoolFalseRefl churchBoolFalseEqNormal rfl

theorem church_nat_zero_eq_decides_normal :
    decideClosedBetaConv 8 churchNatZeroEq churchNatZeroEqNormal = true := by
  rfl

theorem church_nat_one_eq_decides_normal :
    decideClosedBetaConv 8 churchNatOneEq churchNatOneEqNormal = true := by
  rfl

theorem church_nat_zero_one_eq_decides_normal :
    decideClosedBetaConv 8 churchNatZeroOneEq churchNatZeroOneEqNormal = true := by
  rfl

theorem church_bool_true_eq_decides_normal :
    decideClosedBetaConv 8 churchBoolTrueEq churchBoolTrueEqNormal = true := by
  rfl

theorem church_bool_false_eq_decides_normal :
    decideClosedBetaConv 8 churchBoolFalseEq churchBoolFalseEqNormal = true := by
  rfl

theorem church_bool_true_false_eq_decides_normal :
    decideClosedBetaConv 8 churchBoolTrueFalseEq churchBoolTrueFalseEqNormal = true := by
  rfl

theorem church_nat_zero_eq_normal_decides_self :
    decideClosedBetaConv 1 churchNatZeroEqNormal churchNatZeroEqNormal = true := by
  rfl

theorem church_bool_true_eq_normal_decides_self :
    decideClosedBetaConv 1 churchBoolTrueEqNormal churchBoolTrueEqNormal = true := by
  rfl

theorem church_nat_zero_one_normal_separates_zero_zero :
    decideClosedBetaConv 1
      churchNatZeroOneEqNormal
      churchNatZeroEqNormal = false := by
  rfl

theorem church_bool_true_false_normal_separates_true_true :
    decideClosedBetaConv 1
      churchBoolTrueFalseEqNormal
      churchBoolTrueEqNormal = false := by
  rfl

theorem church_nat_zero_eq_separates_bool_true_eq :
    decideClosedBetaConv 1
      churchNatZeroEqNormal
      churchBoolTrueEqNormal = false := by
  rfl

theorem church_refl_zero_type_decides_surface :
    decideClosedBetaConv 8
      churchNatZeroEq
      churchNatZeroEqNormal = true := by
  exact church_nat_zero_eq_decides_normal

theorem church_refl_true_type_decides_surface :
    decideClosedBetaConv 8
      churchBoolTrueEq
      churchBoolTrueEqNormal = true := by
  exact church_bool_true_eq_decides_normal

theorem church_refl_false_type_decides_surface :
    decideClosedBetaConv 8
      churchBoolFalseEq
      churchBoolFalseEqNormal = true := by
  exact church_bool_false_eq_decides_normal

end BEDC.MetaCIC
