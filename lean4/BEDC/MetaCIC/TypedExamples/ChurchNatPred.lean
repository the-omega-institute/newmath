import BEDC.MetaCIC.TypedExamples.ChurchNatArith
import BEDC.MetaCIC.TypedExamples.ChurchGallery
import BEDC.MetaCIC.Decidable.CheckClosed

namespace BEDC.MetaCIC

theorem ctx_lookup_length_lt {Γ : Ctx} {i : Idx} {A : Term}
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

theorem hasType_closed_at_context_length {Γ : Ctx} {t A : Term}
    (h : HasType Γ t A) :
    ClosedAt Γ.length t := by
  induction h with
  | sortRule Γ =>
      exact ClosedAt.sortClosed
  | varRule Γ i A hlookup =>
      exact ClosedAt.varClosed (ctx_lookup_length_lt hlookup)
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

abbrev churchNatPairTy : Term :=
  Term.pi Term.sort
    (Term.pi
      (Term.pi churchNatTy
        (Term.pi churchNatTy (Term.var 2)))
      (Term.var 1))

abbrev churchNatPairValue (a b : Term) : Term :=
  churchPairValue churchNatTy churchNatTy a b

abbrev churchNatPairFst (p : Term) : Term :=
  Term.app
    (Term.app (Term.app churchFstTm churchNatTy) churchNatTy)
    p

abbrev churchNatPairSnd (p : Term) : Term :=
  Term.app
    (Term.app (Term.app churchSndTm churchNatTy) churchNatTy)
    p

abbrev church_pred_step : Term :=
  Term.lam churchNatPairTy
    (churchNatPairValue
      (Term.app churchSuccTm (churchNatPairFst (Term.var 0)))
      (churchNatPairFst (Term.var 0)))

abbrev church_pred_init : Term :=
  churchNatPairValue churchZeroTm churchZeroTm

def church_pred : Term :=
  Term.lam churchNatTy
    (churchNatPairSnd
      (Term.app
        (Term.app
          (Term.app (Term.var 0) churchNatPairTy)
          church_pred_step)
        church_pred_init))

def church_sub : Term :=
  Term.lam churchNatTy
    (Term.lam churchNatTy
      (Term.app
        (Term.app
          (Term.app (Term.var 0) churchNatTy)
          church_pred)
        (Term.var 1)))

abbrev church_fact_step : Term :=
  Term.lam churchNatPairTy
    (churchNatPairValue
      (Term.app churchSuccTm (churchNatPairFst (Term.var 0)))
      (Term.app
        (Term.app church_mul
          (Term.app churchSuccTm (churchNatPairFst (Term.var 0))))
        (churchNatPairSnd (Term.var 0))))

abbrev church_fact_init : Term :=
  churchNatPairValue churchZeroTm churchOneTm

def church_fact : Term :=
  Term.lam churchNatTy
    (churchNatPairSnd
      (Term.app
        (Term.app
          (Term.app (Term.var 0) churchNatPairTy)
          church_fact_step)
        church_fact_init))

abbrev church_nat_unop_type_tm : Term :=
  Term.pi churchNatTy churchNatTy

theorem church_nat_pair_ty_type :
    HasType [] churchNatPairTy Term.sort := by
  exact inferTypeCtx_sound [] churchNatPairTy Term.sort rfl

theorem church_pred_init_type :
    HasType [] church_pred_init churchNatPairTy := by
  exact inferTypeCtx_sound [] church_pred_init churchNatPairTy rfl

theorem church_pred_step_type :
    HasType [] church_pred_step (Term.pi churchNatPairTy churchNatPairTy) := by
  exact inferTypeCtx_sound [] church_pred_step
    (Term.pi churchNatPairTy churchNatPairTy) rfl

theorem church_fact_init_type :
    HasType [] church_fact_init churchNatPairTy := by
  exact inferTypeCtx_sound [] church_fact_init churchNatPairTy rfl

theorem church_fact_step_type :
    HasType [] church_fact_step (Term.pi churchNatPairTy churchNatPairTy) := by
  exact inferTypeCtx_sound [] church_fact_step
    (Term.pi churchNatPairTy churchNatPairTy) rfl

theorem church_pred_type :
    HasType [] church_pred church_nat_unop_type_tm := by
  exact inferTypeCtx_sound [] church_pred church_nat_unop_type_tm rfl

theorem church_sub_type :
    HasType [] church_sub church_nat_binop_type_tm := by
  exact inferTypeCtx_sound [] church_sub church_nat_binop_type_tm rfl

theorem church_fact_type :
    HasType [] church_fact church_nat_unop_type_tm := by
  exact inferTypeCtx_sound [] church_fact church_nat_unop_type_tm rfl

theorem church_nat_pair_ty_closed :
    ClosedAt 0 churchNatPairTy := by
  unfold churchNatPairTy
  apply ClosedAt.piClosed
  · exact ClosedAt.sortClosed
  · apply ClosedAt.piClosed
    · apply ClosedAt.piClosed
      · exact closedAt_succ 0 churchNatTy
          ChurchNatRec.church_nat_closed
      · apply ClosedAt.piClosed
        · exact closedAt_succ 1 churchNatTy
            (closedAt_succ 0 churchNatTy
              ChurchNatRec.church_nat_closed)
        · apply ClosedAt.varClosed
          exact Nat.lt_succ_self 2
    · apply ClosedAt.varClosed
      exact Nat.lt_succ_self 1

theorem church_pred_init_closed :
    ClosedAt 0 church_pred_init := by
  exact hasType_closed_at_context_length church_pred_init_type

theorem church_one_closed_local :
    ClosedAt 0 churchOneTm := by
  exact church_one_closed

theorem church_fact_init_closed :
    ClosedAt 0 church_fact_init := by
  exact hasType_closed_at_context_length church_fact_init_type

theorem church_pred_step_closed :
    ClosedAt 0 church_pred_step := by
  exact hasType_closed_at_context_length church_pred_step_type

theorem church_fact_step_closed :
    ClosedAt 0 church_fact_step := by
  exact hasType_closed_at_context_length church_fact_step_type

theorem church_pred_closed :
    ClosedAt 0 church_pred := by
  exact hasType_closed_at_context_length church_pred_type

theorem church_sub_closed :
    ClosedAt 0 church_sub := by
  exact hasType_closed_at_context_length church_sub_type

theorem church_fact_closed :
    ClosedAt 0 church_fact := by
  exact hasType_closed_at_context_length church_fact_type

abbrev church_pred_iter_result (n : Term) : Term :=
  churchNatPairSnd
    (Term.app
      (Term.app
        (Term.app n churchNatPairTy)
        church_pred_step)
      church_pred_init)

abbrev church_fact_iter_result (n : Term) : Term :=
  churchNatPairSnd
    (Term.app
      (Term.app
        (Term.app n churchNatPairTy)
        church_fact_step)
      church_fact_init)

theorem church_pred_after_n (n : Term)
    (_hn : ClosedAt 0 n) :
    substitute 0 n
      (churchNatPairSnd
        (Term.app
          (Term.app
            (Term.app (Term.var 0) churchNatPairTy)
            church_pred_step)
          church_pred_init)) =
      church_pred_iter_result n := by
  unfold church_pred_iter_result churchNatPairSnd
  change
    Term.app
      (Term.app
        (Term.app (substitute 0 n churchSndTm)
          (substitute 0 n churchNatTy))
        (substitute 0 n churchNatTy))
      (Term.app
        (Term.app
          (Term.app n (substitute 0 n churchNatPairTy))
          (substitute 0 n church_pred_step))
        (substitute 0 n church_pred_init)) =
      Term.app
        (Term.app
          (Term.app churchSndTm churchNatTy)
          churchNatTy)
        (Term.app
          (Term.app
            (Term.app n churchNatPairTy)
            church_pred_step)
          church_pred_init)
  rw [substitute_closed 0 n churchSndTm
    (hasType_closed_at_context_length church_snd)]
  rw [substitute_closed 0 n churchNatTy
    ChurchNatRec.church_nat_closed]
  rw [substitute_closed 0 n churchNatPairTy
    church_nat_pair_ty_closed]
  rw [substitute_closed 0 n church_pred_step
    church_pred_step_closed]
  rw [substitute_closed 0 n church_pred_init
    church_pred_init_closed]

theorem church_fact_after_n (n : Term)
    (_hn : ClosedAt 0 n) :
    substitute 0 n
      (churchNatPairSnd
        (Term.app
          (Term.app
            (Term.app (Term.var 0) churchNatPairTy)
            church_fact_step)
          church_fact_init)) =
      church_fact_iter_result n := by
  unfold church_fact_iter_result churchNatPairSnd
  change
    Term.app
      (Term.app
        (Term.app (substitute 0 n churchSndTm)
          (substitute 0 n churchNatTy))
        (substitute 0 n churchNatTy))
      (Term.app
        (Term.app
          (Term.app n (substitute 0 n churchNatPairTy))
          (substitute 0 n church_fact_step))
        (substitute 0 n church_fact_init)) =
      Term.app
        (Term.app
          (Term.app churchSndTm churchNatTy)
          churchNatTy)
        (Term.app
          (Term.app
            (Term.app n churchNatPairTy)
            church_fact_step)
          church_fact_init)
  rw [substitute_closed 0 n churchSndTm
    (hasType_closed_at_context_length church_snd)]
  rw [substitute_closed 0 n churchNatTy
    ChurchNatRec.church_nat_closed]
  rw [substitute_closed 0 n churchNatPairTy
    church_nat_pair_ty_closed]
  rw [substitute_closed 0 n church_fact_step
    church_fact_step_closed]
  rw [substitute_closed 0 n church_fact_init
    church_fact_init_closed]

theorem church_pred_apply (n : Term)
    (hn : ClosedAt 0 n) :
    BetaStarStep
      (Term.app church_pred n)
      (church_pred_iter_result n) := by
  unfold church_pred
  apply BetaStarStep.step
  · exact BetaStep.beta churchNatTy
      (churchNatPairSnd
        (Term.app
          (Term.app
            (Term.app (Term.var 0) churchNatPairTy)
            church_pred_step)
          church_pred_init))
      n
  rw [church_pred_after_n n hn]
  exact BetaStarStep.refl (church_pred_iter_result n)

theorem church_fact_apply (n : Term)
    (hn : ClosedAt 0 n) :
    BetaStarStep
      (Term.app church_fact n)
      (church_fact_iter_result n) := by
  unfold church_fact
  apply BetaStarStep.step
  · exact BetaStep.beta churchNatTy
      (churchNatPairSnd
        (Term.app
          (Term.app
            (Term.app (Term.var 0) churchNatPairTy)
            church_fact_step)
          church_fact_init))
      n
  rw [church_fact_after_n n hn]
  exact BetaStarStep.refl (church_fact_iter_result n)

theorem church_nat_binary_second_apply (a b : Term)
    (_ha : ClosedAt 0 a) :
    BetaStarStep
      (Term.app
        (Term.app
          (Term.lam churchNatTy
            (Term.lam churchNatTy (Term.var 0)))
          a)
        b)
      b := by
  apply BetaStarStep.step
  · exact BetaStep.congApp1 _ _ b
      (BetaStep.beta churchNatTy
        (Term.lam churchNatTy (Term.var 0))
        a)
  change
    BetaStarStep
      (Term.app
        (Term.lam (substitute 0 a churchNatTy)
          (substitute 1 (shift 0 1 a) (Term.var 0)))
        b)
      b
  rw [substitute_closed 0 a churchNatTy
    ChurchNatRec.church_nat_closed]
  apply BetaStarStep.step
  · exact BetaStep.beta churchNatTy (Term.var 0) b
  exact BetaStarStep.refl b

theorem church_nat_pair_snd_value (a b : Term)
    (ha : ClosedAt 0 a) (hb : ClosedAt 0 b) :
    BetaStarStep
      (churchNatPairSnd (churchNatPairValue a b))
      b := by
  unfold churchNatPairSnd churchSndTm
  apply BetaStarStep.step
  · exact BetaStep.congApp1 _ _ (churchNatPairValue a b)
      (BetaStep.congApp1 _ _ churchNatTy
        (BetaStep.beta Term.sort
          (Term.lam Term.sort
            (Term.lam churchPairABTy
              (Term.app
                (Term.app (Term.var 0) (Term.var 1))
                (Term.lam (Term.var 2)
                  (Term.lam (Term.var 2) (Term.var 0))))))
          churchNatTy))
  change
    BetaStarStep
      (((Term.lam (substitute 0 churchNatTy Term.sort)
            (substitute 1 (shift 0 1 churchNatTy)
              (Term.lam churchPairABTy
                (Term.app
                  (Term.app (Term.var 0) (Term.var 1))
                  (Term.lam (Term.var 2)
                    (Term.lam (Term.var 2) (Term.var 0))))))).app
          churchNatTy).app
        (churchNatPairValue a b))
      b
  rw [shift_closed 0 churchNatTy
    ChurchNatRec.church_nat_closed]
  apply BetaStarStep.step
  · exact BetaStep.congApp1 _ _ (churchNatPairValue a b)
      (BetaStep.beta (substitute 0 churchNatTy Term.sort)
        (substitute 1 churchNatTy
          (Term.lam churchPairABTy
            (Term.app
              (Term.app (Term.var 0) (Term.var 1))
              (Term.lam (Term.var 2)
                (Term.lam (Term.var 2) (Term.var 0))))))
        churchNatTy)
  change
    BetaStarStep
      (Term.app
        (substitute 0 churchNatTy
          (substitute 1 churchNatTy
            (Term.lam churchPairABTy
              (Term.app
                (Term.app (Term.var 0) (Term.var 1))
                (Term.lam (Term.var 2)
                  (Term.lam (Term.var 2) (Term.var 0)))))))
        (churchNatPairValue a b))
      b
  change
    BetaStarStep
      (Term.app
        (Term.lam (substitute 0 churchNatTy
            (substitute 1 churchNatTy churchPairABTy))
          (substitute 1 (shift 0 1 churchNatTy)
            (substitute 2 (shift 0 1 churchNatTy)
              (Term.app
                (Term.app (Term.var 0) (Term.var 1))
                (Term.lam (Term.var 2)
                  (Term.lam (Term.var 2) (Term.var 0)))))))
        (churchNatPairValue a b))
      b
  rw [shift_closed 0 churchNatTy ChurchNatRec.church_nat_closed]
  apply BetaStarStep.step
  · exact BetaStep.beta
      (substitute 0 churchNatTy
        (substitute 1 churchNatTy churchPairABTy))
      (substitute 1 churchNatTy
        (substitute 2 churchNatTy
          (Term.app
            (Term.app (Term.var 0) (Term.var 1))
            (Term.lam (Term.var 2)
              (Term.lam (Term.var 2) (Term.var 0))))))
      (churchNatPairValue a b)
  change
    BetaStarStep
      (Term.app
        (Term.app (churchNatPairValue a b) churchNatTy)
        (Term.lam churchNatTy
          (Term.lam churchNatTy (Term.var 0))))
      b
  exact betaStar_trans
    (church_pair_value_to_selector churchNatTy churchNatTy a b
      churchNatTy
      (Term.lam churchNatTy (Term.lam churchNatTy (Term.var 0)))
      ChurchNatRec.church_nat_closed
      ChurchNatRec.church_nat_closed
      ha hb)
    (church_nat_binary_second_apply a b ha)

theorem church_pred_zero :
    BetaConv (Term.app church_pred churchZeroTm) churchZeroTm := by
  exact BetaConv.of_betaStar_left
    (betaStar_trans
      (church_pred_apply churchZeroTm
        ChurchNatRec.church_zero_closed)
      (betaStar_trans
        (betaStarStep_app_right
          (church_zero_apply churchNatPairTy church_pred_step
            church_pred_init
            church_nat_pair_ty_closed
            church_pred_step_closed
            church_pred_init_closed))
        (church_nat_pair_snd_value churchZeroTm churchZeroTm
          ChurchNatRec.church_zero_closed
          ChurchNatRec.church_zero_closed)))

theorem church_fact_zero :
    BetaConv (Term.app church_fact churchZeroTm) churchOneTm := by
  exact BetaConv.of_betaStar_left
    (betaStar_trans
      (church_fact_apply churchZeroTm
        ChurchNatRec.church_zero_closed)
      (betaStar_trans
        (betaStarStep_app_right
          (church_zero_apply churchNatPairTy church_fact_step
            church_fact_init
            church_nat_pair_ty_closed
            church_fact_step_closed
            church_fact_init_closed))
        (church_nat_pair_snd_value churchZeroTm churchOneTm
          ChurchNatRec.church_zero_closed
          church_one_closed_local)))

abbrev church_sub_iter_result (n m : Term) : Term :=
  Term.app
    (Term.app
      (Term.app m churchNatTy)
      church_pred)
    n

theorem church_sub_after_n (n : Term)
    (hn : ClosedAt 0 n) :
    substitute 0 n
      (Term.lam churchNatTy
        (Term.app
          (Term.app
            (Term.app (Term.var 0) churchNatTy)
            church_pred)
          (Term.var 1))) =
      Term.lam churchNatTy
        (Term.app
          (Term.app
            (Term.app (Term.var 0) churchNatTy)
            church_pred)
          n) := by
  unfold substitute
  rw [shift_closed 0 n hn]
  rw [substitute_closed 0 n churchNatTy
    ChurchNatRec.church_nat_closed]
  change
    Term.lam churchNatTy
      (Term.app
        (Term.app
          (Term.app (Term.var 0)
            (substitute 1 n churchNatTy))
          (substitute 1 n church_pred))
        n) =
      Term.lam churchNatTy
        (Term.app
          (Term.app
            (Term.app (Term.var 0) churchNatTy)
            church_pred)
          n)
  rw [substitute_closed 1 n churchNatTy
    (closedAt_zero_at 1 churchNatTy
      ChurchNatRec.church_nat_closed)]
  rw [substitute_closed 1 n church_pred
    (closedAt_zero_at 1 church_pred church_pred_closed)]

theorem church_sub_payload (n m : Term)
    (hn : ClosedAt 0 n) :
    substitute 0 m
      (Term.app
        (Term.app
          (Term.app (Term.var 0) churchNatTy)
          church_pred)
        n) =
      church_sub_iter_result n m := by
  unfold church_sub_iter_result
  change
    Term.app
      (Term.app
        (Term.app m (substitute 0 m churchNatTy))
        (substitute 0 m church_pred))
      (substitute 0 m n) =
      Term.app
        (Term.app
          (Term.app m churchNatTy)
          church_pred)
        n
  rw [substitute_closed 0 m churchNatTy
    ChurchNatRec.church_nat_closed]
  rw [substitute_closed 0 m church_pred
    church_pred_closed]
  rw [substitute_closed 0 m n hn]

theorem church_sub_apply (n m : Term)
    (hn : ClosedAt 0 n) (_hm : ClosedAt 0 m) :
    BetaStarStep
      (Term.app (Term.app church_sub n) m)
      (church_sub_iter_result n m) := by
  unfold church_sub
  apply BetaStarStep.step
  · exact BetaStep.congApp1 _ _ m
      (BetaStep.beta churchNatTy
        (Term.lam churchNatTy
          (Term.app
            (Term.app
              (Term.app (Term.var 0) churchNatTy)
              church_pred)
            (Term.var 1)))
        n)
  rw [church_sub_after_n n hn]
  apply BetaStarStep.step
  · exact BetaStep.beta churchNatTy
      (Term.app
        (Term.app
          (Term.app (Term.var 0) churchNatTy)
          church_pred)
        n)
      m
  rw [church_sub_payload n m hn]
  exact BetaStarStep.refl (church_sub_iter_result n m)

theorem church_sub_zero (n : Term)
    (hn : ClosedAt 0 n) :
    BetaConv
      (Term.app (Term.app church_sub n) churchZeroTm)
      n := by
  exact BetaConv.of_betaStar_left
    (betaStar_trans
      (church_sub_apply n churchZeroTm hn
        ChurchNatRec.church_zero_closed)
      (church_zero_apply churchNatTy church_pred n
        ChurchNatRec.church_nat_closed
        church_pred_closed
        hn))

theorem church_sub_succ (n m : Term)
    (hn : ClosedAt 0 n) (hm : ClosedAt 0 m) :
    BetaConv
      (Term.app
        (Term.app church_sub n)
        (Term.app churchSuccTm m))
      (Term.app church_pred
        (Term.app (Term.app church_sub n) m)) := by
  let target :=
    Term.app church_pred
      (church_sub_iter_result n m)
  have hSuccM : ClosedAt 0 (Term.app churchSuccTm m) := by
    exact ClosedAt.appClosed ChurchNatRec.church_succ_closed hm
  have hleftCore :
      BetaStarStep
        (Term.app
          (Term.app church_sub n)
          (Term.app churchSuccTm m))
        (church_sub_iter_result n (Term.app churchSuccTm m)) := by
    exact church_sub_apply n (Term.app churchSuccTm m) hn hSuccM
  have hleftIter :
      BetaStarStep
        (church_sub_iter_result n (Term.app churchSuccTm m))
        target := by
    unfold target church_sub_iter_result
    exact ChurchNatRec.church_succ_iter m churchNatTy church_pred n
      hm ChurchNatRec.church_nat_closed church_pred_closed
  have hrightArg :
      BetaStarStep
        (Term.app (Term.app church_sub n) m)
        (church_sub_iter_result n m) := by
    exact church_sub_apply n m hn hm
  have hright :
      BetaStarStep
        (Term.app church_pred
          (Term.app (Term.app church_sub n) m))
        target := by
    unfold target
    exact betaStarStep_app_right hrightArg
  exact
    Exists.intro target
      (And.intro
        (betaStar_trans hleftCore hleftIter)
        hright)

theorem church_pred_succ_iter (n : Term)
    (hn : ClosedAt 0 n) :
    BetaConv
      (Term.app church_pred (Term.app churchSuccTm n))
      (churchNatPairSnd
        (Term.app church_pred_step
          (Term.app
            (Term.app
              (Term.app n churchNatPairTy)
              church_pred_step)
            church_pred_init))) := by
  let target :=
    churchNatPairSnd
      (Term.app church_pred_step
        (Term.app
          (Term.app
            (Term.app n churchNatPairTy)
            church_pred_step)
          church_pred_init))
  have hSuccN : ClosedAt 0 (Term.app churchSuccTm n) := by
    exact ClosedAt.appClosed ChurchNatRec.church_succ_closed hn
  have hcore :
      BetaStarStep
        (Term.app church_pred (Term.app churchSuccTm n))
        (church_pred_iter_result (Term.app churchSuccTm n)) := by
    exact church_pred_apply (Term.app churchSuccTm n) hSuccN
  have hiter :
      BetaStarStep
        (church_pred_iter_result (Term.app churchSuccTm n))
        target := by
    unfold target church_pred_iter_result
    exact betaStarStep_app_right
      (ChurchNatRec.church_succ_iter n churchNatPairTy
          church_pred_step church_pred_init
        hn church_nat_pair_ty_closed church_pred_step_closed)
  exact BetaConv.of_betaStar_left (betaStar_trans hcore hiter)

theorem church_pred_succ (n : Term)
    (hn : ClosedAt 0 n)
    (hstate :
      BetaStarStep
        (churchNatPairSnd
          (Term.app church_pred_step
            (Term.app
              (Term.app
                (Term.app n churchNatPairTy)
                church_pred_step)
              church_pred_init)))
        n) :
    BetaConv (Term.app church_pred (Term.app churchSuccTm n)) n := by
  let target :=
    churchNatPairSnd
      (Term.app church_pred_step
        (Term.app
          (Term.app
            (Term.app n churchNatPairTy)
            church_pred_step)
          church_pred_init))
  have hSuccN : ClosedAt 0 (Term.app churchSuccTm n) := by
    exact ClosedAt.appClosed ChurchNatRec.church_succ_closed hn
  have hcore :
      BetaStarStep
        (Term.app church_pred (Term.app churchSuccTm n))
        (church_pred_iter_result (Term.app churchSuccTm n)) := by
    exact church_pred_apply (Term.app churchSuccTm n) hSuccN
  have hiter :
      BetaStarStep
        (church_pred_iter_result (Term.app churchSuccTm n))
        target := by
    unfold target church_pred_iter_result
    exact betaStarStep_app_right
      (ChurchNatRec.church_succ_iter n churchNatPairTy
        church_pred_step church_pred_init
        hn church_nat_pair_ty_closed church_pred_step_closed)
  exact BetaConv.of_betaStar_left
    (betaStar_trans (betaStar_trans hcore hiter) hstate)

theorem church_fact_succ (n : Term)
    (hn : ClosedAt 0 n) :
    BetaConv
      (Term.app church_fact (Term.app churchSuccTm n))
      (churchNatPairSnd
        (Term.app church_fact_step
          (Term.app
            (Term.app
              (Term.app n churchNatPairTy)
              church_fact_step)
            church_fact_init))) := by
  let target :=
    churchNatPairSnd
      (Term.app church_fact_step
        (Term.app
          (Term.app
            (Term.app n churchNatPairTy)
            church_fact_step)
          church_fact_init))
  have hSuccN : ClosedAt 0 (Term.app churchSuccTm n) := by
    exact ClosedAt.appClosed ChurchNatRec.church_succ_closed hn
  have hcore :
      BetaStarStep
        (Term.app church_fact (Term.app churchSuccTm n))
        (church_fact_iter_result (Term.app churchSuccTm n)) := by
    exact church_fact_apply (Term.app churchSuccTm n) hSuccN
  have hiter :
      BetaStarStep
        (church_fact_iter_result (Term.app churchSuccTm n))
        target := by
    unfold target church_fact_iter_result
    exact betaStarStep_app_right
      (ChurchNatRec.church_succ_iter n churchNatPairTy
        church_fact_step church_fact_init
        hn church_nat_pair_ty_closed church_fact_step_closed)
  exact BetaConv.of_betaStar_left (betaStar_trans hcore hiter)

end BEDC.MetaCIC
