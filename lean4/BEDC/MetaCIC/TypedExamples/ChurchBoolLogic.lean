import BEDC.MetaCIC.TypedExamples.ChurchGallery
import BEDC.MetaCIC.TypedExamples.ChurchAlgebra
import BEDC.MetaCIC.Beta
import BEDC.MetaCIC.Beta.Conversion
import BEDC.MetaCIC.Decidable.CheckClosed

namespace BEDC.MetaCIC

abbrev churchBoolBinopTy : Term :=
  Term.pi churchBoolTy (Term.pi churchBoolTy churchBoolTy)

abbrev boolApply (b X x y : Term) : Term :=
  Term.app (Term.app (Term.app b X) x) y

def church_and : Term :=
  Term.lam churchBoolTy
    (Term.lam churchBoolTy
      (boolApply (Term.var 1) churchBoolTy (Term.var 0) churchFalseTm))

def church_or : Term :=
  Term.lam churchBoolTy
    (Term.lam churchBoolTy
      (boolApply (Term.var 1) churchBoolTy churchTrueTm (Term.var 0)))

def church_not : Term :=
  Term.lam churchBoolTy
    (Term.lam Term.sort
      (Term.lam (Term.var 0)
        (Term.lam (Term.var 1)
          (boolApply (Term.var 3) (Term.var 2) (Term.var 0) (Term.var 1)))))

def church_xor : Term :=
  Term.lam churchBoolTy
    (Term.lam churchBoolTy
      (boolApply (Term.var 1) churchBoolTy
        (Term.app church_not (Term.var 0))
        (Term.var 0)))

theorem church_bool_ty_closed :
    ClosedAt 0 churchBoolTy := by
  unfold churchBoolTy
  apply ClosedAt.piClosed
  · exact ClosedAt.sortClosed
  · apply ClosedAt.piClosed
    · apply ClosedAt.varClosed
      exact Nat.zero_lt_succ 0
    · apply ClosedAt.piClosed
      · apply ClosedAt.varClosed
        exact Nat.lt_succ_self 1
      · apply ClosedAt.varClosed
        exact Nat.lt_succ_self 2

theorem church_true_closed :
    ClosedAt 0 churchTrueTm := by
  unfold churchTrueTm
  apply ClosedAt.lamClosed
  · exact ClosedAt.sortClosed
  · apply ClosedAt.lamClosed
    · apply ClosedAt.varClosed
      exact Nat.zero_lt_succ 0
    · apply ClosedAt.lamClosed
      · apply ClosedAt.varClosed
        exact Nat.lt_succ_self 1
      · apply ClosedAt.varClosed
        exact Nat.succ_lt_succ (Nat.zero_lt_succ 1)

theorem church_false_closed :
    ClosedAt 0 churchFalseTm := by
  unfold churchFalseTm
  apply ClosedAt.lamClosed
  · exact ClosedAt.sortClosed
  · apply ClosedAt.lamClosed
    · apply ClosedAt.varClosed
      exact Nat.zero_lt_succ 0
    · apply ClosedAt.lamClosed
      · apply ClosedAt.varClosed
        exact Nat.lt_succ_self 1
      · apply ClosedAt.varClosed
        exact Nat.zero_lt_succ 2

theorem church_bool_binop_type :
    HasType [] churchBoolBinopTy Term.sort := by
  exact inferTypeCtx_sound [] churchBoolBinopTy Term.sort rfl

theorem church_and_type :
    HasType [] church_and churchBoolBinopTy := by
  exact inferTypeCtx_sound [] church_and churchBoolBinopTy rfl

theorem church_or_type :
    HasType [] church_or churchBoolBinopTy := by
  exact inferTypeCtx_sound [] church_or churchBoolBinopTy rfl

theorem church_not_type :
    HasType [] church_not (Term.pi churchBoolTy churchBoolTy) := by
  exact inferTypeCtx_sound [] church_not (Term.pi churchBoolTy churchBoolTy) rfl

theorem church_xor_type :
    HasType [] church_xor churchBoolBinopTy := by
  exact inferTypeCtx_sound [] church_xor churchBoolBinopTy rfl

theorem church_and_closed :
    ClosedAt 0 church_and := by
  unfold church_and boolApply
  apply ClosedAt.lamClosed
  · exact church_bool_ty_closed
  · apply ClosedAt.lamClosed
    · exact closedAt_succ 0 churchBoolTy church_bool_ty_closed
    · apply ClosedAt.appClosed
      · apply ClosedAt.appClosed
        · apply ClosedAt.appClosed
          · apply ClosedAt.varClosed
            exact Nat.lt_succ_self 1
          · exact closedAt_succ 1 churchBoolTy
              (closedAt_succ 0 churchBoolTy church_bool_ty_closed)
        · apply ClosedAt.varClosed
          exact Nat.zero_lt_succ 1
      · exact closedAt_succ 1 churchFalseTm
          (closedAt_succ 0 churchFalseTm church_false_closed)

theorem church_or_closed :
    ClosedAt 0 church_or := by
  unfold church_or boolApply
  apply ClosedAt.lamClosed
  · exact church_bool_ty_closed
  · apply ClosedAt.lamClosed
    · exact closedAt_succ 0 churchBoolTy church_bool_ty_closed
    · apply ClosedAt.appClosed
      · apply ClosedAt.appClosed
        · apply ClosedAt.appClosed
          · apply ClosedAt.varClosed
            exact Nat.lt_succ_self 1
          · exact closedAt_succ 1 churchBoolTy
              (closedAt_succ 0 churchBoolTy church_bool_ty_closed)
        · exact closedAt_succ 1 churchTrueTm
            (closedAt_succ 0 churchTrueTm church_true_closed)
      · apply ClosedAt.varClosed
        exact Nat.zero_lt_succ 1

theorem church_not_closed :
    ClosedAt 0 church_not := by
  unfold church_not boolApply
  apply ClosedAt.lamClosed
  · exact church_bool_ty_closed
  · apply ClosedAt.lamClosed
    · exact ClosedAt.sortClosed
    · apply ClosedAt.lamClosed
      · apply ClosedAt.varClosed
        exact Nat.zero_lt_succ 1
      · apply ClosedAt.lamClosed
        · apply ClosedAt.varClosed
          exact Nat.succ_lt_succ (Nat.zero_lt_succ 1)
        · apply ClosedAt.appClosed
          · apply ClosedAt.appClosed
            · apply ClosedAt.appClosed
              · apply ClosedAt.varClosed
                exact Nat.lt_succ_self 3
              · apply ClosedAt.varClosed
                exact Nat.succ_lt_succ (Nat.succ_lt_succ (Nat.zero_lt_succ 1))
            · apply ClosedAt.varClosed
              exact Nat.zero_lt_succ 3
          · apply ClosedAt.varClosed
            exact Nat.succ_lt_succ (Nat.zero_lt_succ 2)

theorem church_xor_closed :
    ClosedAt 0 church_xor := by
  unfold church_xor boolApply
  apply ClosedAt.lamClosed
  · exact church_bool_ty_closed
  · apply ClosedAt.lamClosed
    · exact closedAt_succ 0 churchBoolTy church_bool_ty_closed
    · apply ClosedAt.appClosed
      · apply ClosedAt.appClosed
        · apply ClosedAt.appClosed
          · apply ClosedAt.varClosed
            exact Nat.lt_succ_self 1
          · exact closedAt_succ 1 churchBoolTy
              (closedAt_succ 0 churchBoolTy church_bool_ty_closed)
        · apply ClosedAt.appClosed
          · exact closedAt_succ 1 church_not
              (closedAt_succ 0 church_not church_not_closed)
          · apply ClosedAt.varClosed
            exact Nat.zero_lt_succ 1
      · apply ClosedAt.varClosed
        exact Nat.zero_lt_succ 1

theorem church_and_after_left (b : Term)
    (_hb : ClosedAt 0 b) :
    substitute 1 b
      (boolApply (Term.var 1) churchBoolTy (Term.var 0) churchFalseTm) =
      boolApply b churchBoolTy (Term.var 0) churchFalseTm := by
  unfold boolApply
  change
    Term.app
      (Term.app
        (Term.app (substitute 1 b (Term.var 1))
          (substitute 1 b churchBoolTy))
        (Term.var 0))
      (substitute 1 b churchFalseTm) =
      Term.app (Term.app (Term.app b churchBoolTy) (Term.var 0)) churchFalseTm
  rw [substitute_closed 1 b churchBoolTy
    (closedAt_zero_at 1 churchBoolTy church_bool_ty_closed)]
  rw [substitute_closed 1 b churchFalseTm
    (closedAt_zero_at 1 churchFalseTm church_false_closed)]
  rfl

theorem church_and_payload (b c : Term)
    (hb : ClosedAt 0 b) :
    substitute 0 c (boolApply b churchBoolTy (Term.var 0) churchFalseTm) =
      boolApply b churchBoolTy c churchFalseTm := by
  unfold boolApply
  change
    Term.app
      (Term.app
        (Term.app (substitute 0 c b)
          (substitute 0 c churchBoolTy))
        c)
      (substitute 0 c churchFalseTm) =
      Term.app (Term.app (Term.app b churchBoolTy) c) churchFalseTm
  rw [substitute_closed 0 c b hb]
  rw [substitute_closed 0 c churchBoolTy church_bool_ty_closed]
  rw [substitute_closed 0 c churchFalseTm church_false_closed]

theorem church_and_apply (b c : Term)
    (hb : ClosedAt 0 b) (_hc : ClosedAt 0 c) :
    BetaStarStep
      (Term.app (Term.app church_and b) c)
      (boolApply b churchBoolTy c churchFalseTm) := by
  unfold church_and
  apply BetaStarStep.step
  · exact BetaStep.congApp1 _ _ c
      (BetaStep.beta churchBoolTy
        (Term.lam churchBoolTy
          (boolApply (Term.var 1) churchBoolTy (Term.var 0) churchFalseTm))
        b)
  unfold substitute
  rw [shift_closed 0 b hb]
  rw [substitute_closed 0 b churchBoolTy church_bool_ty_closed]
  apply BetaStarStep.step
  · exact BetaStep.beta
      (substitute 0 b churchBoolTy)
      (substitute (0 + 1) b
        (boolApply (Term.var 1) churchBoolTy (Term.var 0) churchFalseTm))
      c
  rw [church_and_after_left b hb]
  rw [church_and_payload b c hb]
  exact BetaStarStep.refl (boolApply b churchBoolTy c churchFalseTm)

theorem church_or_after_left (b : Term)
    (_hb : ClosedAt 0 b) :
    substitute 1 b
      (boolApply (Term.var 1) churchBoolTy churchTrueTm (Term.var 0)) =
      boolApply b churchBoolTy churchTrueTm (Term.var 0) := by
  unfold boolApply
  change
    Term.app
      (Term.app
        (Term.app (substitute 1 b (Term.var 1))
          (substitute 1 b churchBoolTy))
        (substitute 1 b churchTrueTm))
      (Term.var 0) =
      Term.app (Term.app (Term.app b churchBoolTy) churchTrueTm) (Term.var 0)
  rw [substitute_closed 1 b churchBoolTy
    (closedAt_zero_at 1 churchBoolTy church_bool_ty_closed)]
  rw [substitute_closed 1 b churchTrueTm
    (closedAt_zero_at 1 churchTrueTm church_true_closed)]
  rfl

theorem church_or_payload (b c : Term)
    (hb : ClosedAt 0 b) :
    substitute 0 c (boolApply b churchBoolTy churchTrueTm (Term.var 0)) =
      boolApply b churchBoolTy churchTrueTm c := by
  unfold boolApply
  change
    Term.app
      (Term.app
        (Term.app (substitute 0 c b)
          (substitute 0 c churchBoolTy))
        (substitute 0 c churchTrueTm))
      c =
      Term.app (Term.app (Term.app b churchBoolTy) churchTrueTm) c
  rw [substitute_closed 0 c b hb]
  rw [substitute_closed 0 c churchBoolTy church_bool_ty_closed]
  rw [substitute_closed 0 c churchTrueTm church_true_closed]

theorem church_or_apply (b c : Term)
    (hb : ClosedAt 0 b) (_hc : ClosedAt 0 c) :
    BetaStarStep
      (Term.app (Term.app church_or b) c)
      (boolApply b churchBoolTy churchTrueTm c) := by
  unfold church_or
  apply BetaStarStep.step
  · exact BetaStep.congApp1 _ _ c
      (BetaStep.beta churchBoolTy
        (Term.lam churchBoolTy
          (boolApply (Term.var 1) churchBoolTy churchTrueTm (Term.var 0)))
        b)
  unfold substitute
  rw [shift_closed 0 b hb]
  rw [substitute_closed 0 b churchBoolTy church_bool_ty_closed]
  apply BetaStarStep.step
  · exact BetaStep.beta
      (substitute 0 b churchBoolTy)
      (substitute (0 + 1) b
        (boolApply (Term.var 1) churchBoolTy churchTrueTm (Term.var 0)))
      c
  rw [church_or_after_left b hb]
  rw [church_or_payload b c hb]
  exact BetaStarStep.refl (boolApply b churchBoolTy churchTrueTm c)

theorem church_not_after_bool (b : Term)
    (_hb : ClosedAt 0 b) :
    substitute 0 b
      (Term.lam Term.sort
        (Term.lam (Term.var 0)
          (Term.lam (Term.var 1)
            (boolApply (Term.var 3) (Term.var 2) (Term.var 0) (Term.var 1))))) =
      Term.lam Term.sort
        (Term.lam (Term.var 0)
          (Term.lam (Term.var 1)
            (boolApply
              (shift 0 1 (shift 0 1 (shift 0 1 b)))
              (Term.var 2) (Term.var 0) (Term.var 1)))) := by
  unfold boolApply
  change
    Term.lam Term.sort
      (Term.lam (Term.var 0)
        (Term.lam (Term.var 1)
          (Term.app
            (Term.app
              (Term.app (substitute 3 (shift 0 1 (shift 0 1 (shift 0 1 b)))
                (Term.var 3))
                (Term.var 2))
              (Term.var 0))
            (Term.var 1)))) =
      Term.lam Term.sort
        (Term.lam (Term.var 0)
          (Term.lam (Term.var 1)
            (Term.app
              (Term.app
                (Term.app (shift 0 1 (shift 0 1 (shift 0 1 b))) (Term.var 2))
                (Term.var 0))
              (Term.var 1))))
  rfl

theorem church_not_apply (b : Term)
    (hb : ClosedAt 0 b) :
    BetaStarStep (Term.app church_not b)
      (Term.lam Term.sort
        (Term.lam (Term.var 0)
          (Term.lam (Term.var 1)
            (boolApply b (Term.var 2) (Term.var 0) (Term.var 1))))) := by
  unfold church_not
  apply BetaStarStep.step
  · exact BetaStep.beta churchBoolTy
      (Term.lam Term.sort
        (Term.lam (Term.var 0)
          (Term.lam (Term.var 1)
            (boolApply (Term.var 3) (Term.var 2) (Term.var 0) (Term.var 1)))))
      b
  rw [church_not_after_bool b hb]
  rw [shift_zero_three_closed b hb]
  exact BetaStarStep.refl
    (Term.lam Term.sort
      (Term.lam (Term.var 0)
        (Term.lam (Term.var 1)
          (boolApply b (Term.var 2) (Term.var 0) (Term.var 1)))))

theorem church_xor_after_left (b : Term)
    (_hb : ClosedAt 0 b) :
    substitute 1 b
      (boolApply (Term.var 1) churchBoolTy
        (Term.app church_not (Term.var 0))
        (Term.var 0)) =
      boolApply b churchBoolTy
        (Term.app church_not (Term.var 0))
        (Term.var 0) := by
  unfold boolApply
  change
    Term.app
      (Term.app
        (Term.app (substitute 1 b (Term.var 1))
          (substitute 1 b churchBoolTy))
        (Term.app (substitute 1 b church_not) (Term.var 0)))
      (Term.var 0) =
      Term.app
        (Term.app
          (Term.app b churchBoolTy)
          (Term.app church_not (Term.var 0)))
        (Term.var 0)
  rw [substitute_closed 1 b churchBoolTy
    (closedAt_zero_at 1 churchBoolTy church_bool_ty_closed)]
  rw [substitute_closed 1 b church_not
    (closedAt_zero_at 1 church_not church_not_closed)]
  rfl

theorem church_xor_payload (b c : Term)
    (hb : ClosedAt 0 b) :
    substitute 0 c
      (boolApply b churchBoolTy
        (Term.app church_not (Term.var 0))
        (Term.var 0)) =
      boolApply b churchBoolTy (Term.app church_not c) c := by
  unfold boolApply
  change
    Term.app
      (Term.app
        (Term.app (substitute 0 c b)
          (substitute 0 c churchBoolTy))
        (Term.app (substitute 0 c church_not) c))
      c =
      Term.app
        (Term.app
          (Term.app b churchBoolTy)
          (Term.app church_not c))
        c
  rw [substitute_closed 0 c b hb]
  rw [substitute_closed 0 c churchBoolTy church_bool_ty_closed]
  rw [substitute_closed 0 c church_not church_not_closed]

theorem church_xor_apply (b c : Term)
    (hb : ClosedAt 0 b) (_hc : ClosedAt 0 c) :
    BetaStarStep
      (Term.app (Term.app church_xor b) c)
      (boolApply b churchBoolTy (Term.app church_not c) c) := by
  unfold church_xor
  apply BetaStarStep.step
  · exact BetaStep.congApp1 _ _ c
      (BetaStep.beta churchBoolTy
        (Term.lam churchBoolTy
          (boolApply (Term.var 1) churchBoolTy
            (Term.app church_not (Term.var 0))
            (Term.var 0)))
        b)
  unfold substitute
  rw [shift_closed 0 b hb]
  rw [substitute_closed 0 b churchBoolTy church_bool_ty_closed]
  apply BetaStarStep.step
  · exact BetaStep.beta
      (substitute 0 b churchBoolTy)
      (substitute (0 + 1) b
        (boolApply (Term.var 1) churchBoolTy
          (Term.app church_not (Term.var 0))
          (Term.var 0)))
      c
  rw [church_xor_after_left b hb]
  rw [church_xor_payload b c hb]
  exact BetaStarStep.refl (boolApply b churchBoolTy (Term.app church_not c) c)

theorem true_swap_open :
    BetaStarStep
      (boolApply churchTrueTm (Term.var 2) (Term.var 0) (Term.var 1))
      (Term.var 0) := by
  unfold boolApply churchTrueTm
  apply BetaStarStep.step
  · exact BetaStep.congApp1 _ _ (Term.var 1)
      (BetaStep.congApp1 _ _ (Term.var 0)
        (BetaStep.beta Term.sort
          (Term.lam (Term.var 0)
            (Term.lam (Term.var 1) (Term.var 1)))
          (Term.var 2)))
  unfold substitute
  apply BetaStarStep.step
  · exact BetaStep.congApp1 _ _ (Term.var 1)
      (BetaStep.beta (Term.var 2) (Term.lam (Term.var 3) (Term.var 1))
        (Term.var 0))
  apply BetaStarStep.step
  · exact BetaStep.beta (Term.var 2) (Term.var 1) (Term.var 1)
  exact BetaStarStep.refl (Term.var 0)

theorem false_swap_open :
    BetaStarStep
      (boolApply churchFalseTm (Term.var 2) (Term.var 0) (Term.var 1))
      (Term.var 1) := by
  unfold boolApply churchFalseTm
  apply BetaStarStep.step
  · exact BetaStep.congApp1 _ _ (Term.var 1)
      (BetaStep.congApp1 _ _ (Term.var 0)
        (BetaStep.beta Term.sort
          (Term.lam (Term.var 0)
            (Term.lam (Term.var 1) (Term.var 0)))
          (Term.var 2)))
  unfold substitute
  apply BetaStarStep.step
  · exact BetaStep.congApp1 _ _ (Term.var 1)
      (BetaStep.beta (Term.var 2) (Term.lam (Term.var 3) (Term.var 0))
        (Term.var 0))
  apply BetaStarStep.step
  · exact BetaStep.beta (Term.var 2) (Term.var 0) (Term.var 1)
  exact BetaStarStep.refl (Term.var 1)

theorem church_not_true_star :
    BetaStarStep (Term.app church_not churchTrueTm) churchFalseTm := by
  exact betaStar_trans
    (church_not_apply churchTrueTm church_true_closed)
    (betaStarStep_lam_cong
      (betaStarStep_lam_cong
        (betaStarStep_lam_cong true_swap_open)))

theorem church_not_false_star :
    BetaStarStep (Term.app church_not churchFalseTm) churchTrueTm := by
  exact betaStar_trans
    (church_not_apply churchFalseTm church_false_closed)
    (betaStarStep_lam_cong
      (betaStarStep_lam_cong
        (betaStarStep_lam_cong false_swap_open)))

theorem church_and_true_true :
    BetaConv (Term.app (Term.app church_and churchTrueTm) churchTrueTm) churchTrueTm := by
  exact BetaConv.of_betaStar_left
    (betaStar_trans
      (church_and_apply churchTrueTm churchTrueTm church_true_closed church_true_closed)
      (church_true_proj churchBoolTy churchTrueTm churchFalseTm
        church_bool_ty_closed church_true_closed church_false_closed))

theorem church_and_true_false :
    BetaConv (Term.app (Term.app church_and churchTrueTm) churchFalseTm) churchFalseTm := by
  exact BetaConv.of_betaStar_left
    (betaStar_trans
      (church_and_apply churchTrueTm churchFalseTm church_true_closed church_false_closed)
      (church_true_proj churchBoolTy churchFalseTm churchFalseTm
        church_bool_ty_closed church_false_closed church_false_closed))

theorem church_and_false_true :
    BetaConv (Term.app (Term.app church_and churchFalseTm) churchTrueTm) churchFalseTm := by
  exact BetaConv.of_betaStar_left
    (betaStar_trans
      (church_and_apply churchFalseTm churchTrueTm church_false_closed church_true_closed)
      (church_false_proj churchBoolTy churchTrueTm churchFalseTm
        church_bool_ty_closed church_true_closed church_false_closed))

theorem church_and_false_false :
    BetaConv (Term.app (Term.app church_and churchFalseTm) churchFalseTm) churchFalseTm := by
  exact BetaConv.of_betaStar_left
    (betaStar_trans
      (church_and_apply churchFalseTm churchFalseTm church_false_closed church_false_closed)
      (church_false_proj churchBoolTy churchFalseTm churchFalseTm
        church_bool_ty_closed church_false_closed church_false_closed))

theorem church_and_false_x (x : Term) (hx : ClosedAt 0 x) :
    BetaConv (Term.app (Term.app church_and churchFalseTm) x) churchFalseTm := by
  exact BetaConv.of_betaStar_left
    (betaStar_trans
      (church_and_apply churchFalseTm x church_false_closed hx)
      (church_false_proj churchBoolTy x churchFalseTm
        church_bool_ty_closed hx church_false_closed))

theorem church_or_true_true :
    BetaConv (Term.app (Term.app church_or churchTrueTm) churchTrueTm) churchTrueTm := by
  exact BetaConv.of_betaStar_left
    (betaStar_trans
      (church_or_apply churchTrueTm churchTrueTm church_true_closed church_true_closed)
      (church_true_proj churchBoolTy churchTrueTm churchTrueTm
        church_bool_ty_closed church_true_closed church_true_closed))

theorem church_or_true_false :
    BetaConv (Term.app (Term.app church_or churchTrueTm) churchFalseTm) churchTrueTm := by
  exact BetaConv.of_betaStar_left
    (betaStar_trans
      (church_or_apply churchTrueTm churchFalseTm church_true_closed church_false_closed)
      (church_true_proj churchBoolTy churchTrueTm churchFalseTm
        church_bool_ty_closed church_true_closed church_false_closed))

theorem church_or_false_true :
    BetaConv (Term.app (Term.app church_or churchFalseTm) churchTrueTm) churchTrueTm := by
  exact BetaConv.of_betaStar_left
    (betaStar_trans
      (church_or_apply churchFalseTm churchTrueTm church_false_closed church_true_closed)
      (church_false_proj churchBoolTy churchTrueTm churchTrueTm
        church_bool_ty_closed church_true_closed church_true_closed))

theorem church_or_false_false :
    BetaConv (Term.app (Term.app church_or churchFalseTm) churchFalseTm) churchFalseTm := by
  exact BetaConv.of_betaStar_left
    (betaStar_trans
      (church_or_apply churchFalseTm churchFalseTm church_false_closed church_false_closed)
      (church_false_proj churchBoolTy churchTrueTm churchFalseTm
        church_bool_ty_closed church_true_closed church_false_closed))

theorem church_not_true :
    BetaConv (Term.app church_not churchTrueTm) churchFalseTm := by
  exact BetaConv.of_betaStar_left church_not_true_star

theorem church_not_false :
    BetaConv (Term.app church_not churchFalseTm) churchTrueTm := by
  exact BetaConv.of_betaStar_left church_not_false_star

theorem church_xor_true_true :
    BetaConv (Term.app (Term.app church_xor churchTrueTm) churchTrueTm) churchFalseTm := by
  exact BetaConv.of_betaStar_left
    (betaStar_trans
      (church_xor_apply churchTrueTm churchTrueTm church_true_closed church_true_closed)
      (betaStar_trans
        (church_true_proj churchBoolTy
          (Term.app church_not churchTrueTm) churchTrueTm
          church_bool_ty_closed
          (ClosedAt.appClosed church_not_closed church_true_closed)
          church_true_closed)
        church_not_true_star))

theorem church_xor_true_false :
    BetaConv (Term.app (Term.app church_xor churchTrueTm) churchFalseTm) churchTrueTm := by
  exact BetaConv.of_betaStar_left
    (betaStar_trans
      (church_xor_apply churchTrueTm churchFalseTm church_true_closed church_false_closed)
      (betaStar_trans
        (church_true_proj churchBoolTy
          (Term.app church_not churchFalseTm) churchFalseTm
          church_bool_ty_closed
          (ClosedAt.appClosed church_not_closed church_false_closed)
          church_false_closed)
        church_not_false_star))

theorem church_xor_false_true :
    BetaConv (Term.app (Term.app church_xor churchFalseTm) churchTrueTm) churchTrueTm := by
  exact BetaConv.of_betaStar_left
    (betaStar_trans
      (church_xor_apply churchFalseTm churchTrueTm church_false_closed church_true_closed)
      (church_false_proj churchBoolTy
        (Term.app church_not churchTrueTm) churchTrueTm
        church_bool_ty_closed
        (ClosedAt.appClosed church_not_closed church_true_closed)
        church_true_closed))

theorem church_xor_false_false :
    BetaConv (Term.app (Term.app church_xor churchFalseTm) churchFalseTm) churchFalseTm := by
  exact BetaConv.of_betaStar_left
    (betaStar_trans
      (church_xor_apply churchFalseTm churchFalseTm church_false_closed church_false_closed)
      (church_false_proj churchBoolTy
        (Term.app church_not churchFalseTm) churchFalseTm
        church_bool_ty_closed
        (ClosedAt.appClosed church_not_closed church_false_closed)
        church_false_closed))

end BEDC.MetaCIC
