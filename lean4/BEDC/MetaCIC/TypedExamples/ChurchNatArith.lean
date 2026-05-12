import BEDC.MetaCIC.TypedExamples.ChurchNatRec
import BEDC.MetaCIC.TypedExamples.ChurchAlgebra
import BEDC.MetaCIC.Decidable.CheckClosed

namespace BEDC.MetaCIC

def church_mul : Term :=
  Term.lam churchNatTy
    (Term.lam churchNatTy
      (Term.app
        (Term.app
          (Term.app (Term.var 1) churchNatTy)
          (Term.app ChurchNatRec.church_add (Term.var 0)))
        churchZeroTm))

def church_exp : Term :=
  Term.lam churchNatTy
    (Term.lam churchNatTy
      (Term.app
        (Term.app
          (Term.app (Term.var 0) churchNatTy)
          (Term.app church_mul (Term.var 1)))
        churchOneTm))

abbrev church_nat_binop_type_tm : Term :=
  Term.pi churchNatTy (Term.pi churchNatTy churchNatTy)

theorem church_add_closed :
    ClosedAt 0 ChurchNatRec.church_add := by
  unfold ChurchNatRec.church_add
  apply ClosedAt.lamClosed
  · exact ChurchNatRec.church_nat_closed
  · apply ClosedAt.lamClosed
    · exact closedAt_succ 0 churchNatTy ChurchNatRec.church_nat_closed
    · apply ClosedAt.appClosed
      · apply ClosedAt.appClosed
        · apply ClosedAt.appClosed
          · apply ClosedAt.varClosed
            exact Nat.lt_succ_self 1
          · exact closedAt_succ 1 churchNatTy
              (closedAt_succ 0 churchNatTy ChurchNatRec.church_nat_closed)
        · exact closedAt_succ 1 churchSuccTm
            (closedAt_succ 0 churchSuccTm ChurchNatRec.church_succ_closed)
      · apply ClosedAt.varClosed
        exact Nat.zero_lt_succ 1

theorem church_one_closed :
    ClosedAt 0 churchOneTm := by
  unfold churchOneTm
  apply ClosedAt.lamClosed
  · exact ClosedAt.sortClosed
  · apply ClosedAt.lamClosed
    · apply ClosedAt.piClosed
      · apply ClosedAt.varClosed
        exact Nat.zero_lt_succ 0
      · apply ClosedAt.varClosed
        exact Nat.lt_succ_self 1
    · apply ClosedAt.lamClosed
      · apply ClosedAt.varClosed
        exact Nat.lt_succ_self 1
      · apply ClosedAt.appClosed
        · apply ClosedAt.varClosed
          exact Nat.succ_lt_succ (Nat.zero_lt_succ 1)
        · apply ClosedAt.varClosed
          exact Nat.zero_lt_succ 2

theorem church_mul_closed :
    ClosedAt 0 church_mul := by
  unfold church_mul
  apply ClosedAt.lamClosed
  · exact ChurchNatRec.church_nat_closed
  · apply ClosedAt.lamClosed
    · exact closedAt_succ 0 churchNatTy ChurchNatRec.church_nat_closed
    · apply ClosedAt.appClosed
      · apply ClosedAt.appClosed
        · apply ClosedAt.appClosed
          · apply ClosedAt.varClosed
            exact Nat.lt_succ_self 1
          · exact closedAt_succ 1 churchNatTy
              (closedAt_succ 0 churchNatTy ChurchNatRec.church_nat_closed)
        · apply ClosedAt.appClosed
          · exact closedAt_succ 1 ChurchNatRec.church_add
              (closedAt_succ 0 ChurchNatRec.church_add
                church_add_closed)
          · apply ClosedAt.varClosed
            exact Nat.zero_lt_succ 1
      · exact closedAt_succ 1 churchZeroTm
          (closedAt_succ 0 churchZeroTm ChurchNatRec.church_zero_closed)

theorem church_exp_closed :
    ClosedAt 0 church_exp := by
  unfold church_exp
  apply ClosedAt.lamClosed
  · exact ChurchNatRec.church_nat_closed
  · apply ClosedAt.lamClosed
    · exact closedAt_succ 0 churchNatTy ChurchNatRec.church_nat_closed
    · apply ClosedAt.appClosed
      · apply ClosedAt.appClosed
        · apply ClosedAt.appClosed
          · apply ClosedAt.varClosed
            exact Nat.zero_lt_succ 1
          · exact closedAt_succ 1 churchNatTy
              (closedAt_succ 0 churchNatTy ChurchNatRec.church_nat_closed)
        · apply ClosedAt.appClosed
          · exact closedAt_succ 1 church_mul
              (closedAt_succ 0 church_mul church_mul_closed)
          · apply ClosedAt.varClosed
            exact Nat.lt_succ_self 1
      · exact closedAt_succ 1 churchOneTm
          (closedAt_succ 0 churchOneTm church_one_closed)

theorem church_nat_binop_type :
    HasType [] church_nat_binop_type_tm Term.sort := by
  unfold church_nat_binop_type_tm
  apply HasType.piRule
  · exact church_nat_type
  · apply HasType.piRule
    · exact church_nat_type_in_ctx
    · exact ChurchNatRec.church_nat_type_in_two_ctx

theorem church_mul_type :
    HasType [] church_mul church_nat_binop_type_tm := by
  exact inferTypeCtx_sound [] church_mul church_nat_binop_type_tm rfl

theorem church_exp_type :
    HasType [] church_exp church_nat_binop_type_tm := by
  exact inferTypeCtx_sound [] church_exp church_nat_binop_type_tm rfl

theorem church_mul_after_n (n : Term) :
    substitute 1 n
      (Term.app
        (Term.app
          (Term.app (Term.var 1) churchNatTy)
          (Term.app ChurchNatRec.church_add (Term.var 0)))
        churchZeroTm) =
      Term.app
        (Term.app
          (Term.app n churchNatTy)
          (Term.app ChurchNatRec.church_add (Term.var 0)))
        churchZeroTm := by
  change
    Term.app
      (Term.app
        (Term.app (substitute 1 n (Term.var 1))
          (substitute 1 n churchNatTy))
        (substitute 1 n (Term.app ChurchNatRec.church_add (Term.var 0))))
      (substitute 1 n churchZeroTm) =
      Term.app
        (Term.app
          (Term.app n churchNatTy)
          (Term.app ChurchNatRec.church_add (Term.var 0)))
        churchZeroTm
  rw [substitute_closed 1 n churchNatTy
    (closedAt_zero_at 1 churchNatTy ChurchNatRec.church_nat_closed)]
  change
    Term.app
      (Term.app
        (Term.app (substitute 1 n (Term.var 1)) churchNatTy)
        (Term.app (substitute 1 n ChurchNatRec.church_add) (Term.var 0)))
      (substitute 1 n churchZeroTm) =
      Term.app
        (Term.app
          (Term.app n churchNatTy)
          (Term.app ChurchNatRec.church_add (Term.var 0)))
        churchZeroTm
  rw [substitute_closed 1 n ChurchNatRec.church_add
    (closedAt_zero_at 1 ChurchNatRec.church_add church_add_closed)]
  rw [substitute_closed 1 n churchZeroTm
    (closedAt_zero_at 1 churchZeroTm ChurchNatRec.church_zero_closed)]
  rfl

theorem church_mul_payload (n m : Term)
    (hn : ClosedAt 0 n) :
    substitute 0 m
      (Term.app
        (Term.app
          (Term.app n churchNatTy)
          (Term.app ChurchNatRec.church_add (Term.var 0)))
        churchZeroTm) =
      Term.app
        (Term.app
          (Term.app n churchNatTy)
          (Term.app ChurchNatRec.church_add m))
        churchZeroTm := by
  change
    Term.app
      (Term.app
        (Term.app (substitute 0 m n)
          (substitute 0 m churchNatTy))
        (Term.app
          (substitute 0 m ChurchNatRec.church_add)
          m))
      (substitute 0 m churchZeroTm) =
      Term.app
        (Term.app
          (Term.app n churchNatTy)
          (Term.app ChurchNatRec.church_add m))
        churchZeroTm
  rw [substitute_closed 0 m n hn]
  rw [substitute_closed 0 m churchNatTy ChurchNatRec.church_nat_closed]
  rw [substitute_closed 0 m ChurchNatRec.church_add
    church_add_closed]
  rw [substitute_closed 0 m churchZeroTm ChurchNatRec.church_zero_closed]

theorem church_mul_apply (n m : Term)
    (hn : ClosedAt 0 n) (_hm : ClosedAt 0 m) :
    BetaStarStep
      (Term.app (Term.app church_mul n) m)
      (Term.app
        (Term.app
          (Term.app n churchNatTy)
          (Term.app ChurchNatRec.church_add m))
        churchZeroTm) := by
  unfold church_mul
  apply BetaStarStep.step
  · exact BetaStep.congApp1 _ _ m
      (BetaStep.beta churchNatTy
        (Term.lam churchNatTy
          (Term.app
            (Term.app
              (Term.app (Term.var 1) churchNatTy)
              (Term.app ChurchNatRec.church_add (Term.var 0)))
            churchZeroTm))
        n)
  unfold substitute
  rw [shift_closed 0 n hn]
  rw [substitute_closed 0 n churchNatTy ChurchNatRec.church_nat_closed]
  apply BetaStarStep.step
  · exact BetaStep.beta
      (substitute 0 n churchNatTy)
      (substitute (0 + 1) n
        (Term.app
          (Term.app
            (Term.app (Term.var 1) churchNatTy)
            (Term.app ChurchNatRec.church_add (Term.var 0)))
          churchZeroTm))
      m
  rw [church_mul_after_n n]
  rw [church_mul_payload n m hn]
  exact BetaStarStep.refl
    (Term.app
      (Term.app
        (Term.app n churchNatTy)
        (Term.app ChurchNatRec.church_add m))
      churchZeroTm)

theorem church_mul_zero (m : Term)
    (hm : ClosedAt 0 m) :
    BetaStarStep (Term.app (Term.app church_mul churchZeroTm) m) churchZeroTm := by
  exact betaStar_trans
    (church_mul_apply churchZeroTm m ChurchNatRec.church_zero_closed hm)
    (church_zero_apply churchNatTy (Term.app ChurchNatRec.church_add m)
      churchZeroTm
      ChurchNatRec.church_nat_closed
      (ClosedAt.appClosed
        church_add_closed
        hm)
      ChurchNatRec.church_zero_closed)

theorem church_mul_succ_left (n m : Term)
    (hn : ClosedAt 0 n) (hm : ClosedAt 0 m) :
    BetaConv
      (Term.app (Term.app church_mul (Term.app churchSuccTm n)) m)
      (Term.app
        (Term.app ChurchNatRec.church_add m)
        (Term.app (Term.app church_mul n) m)) := by
  let target :=
    Term.app
      (Term.app ChurchNatRec.church_add m)
      (Term.app
        (Term.app
          (Term.app n churchNatTy)
          (Term.app ChurchNatRec.church_add m))
        churchZeroTm)
  have hSuccN : ClosedAt 0 (Term.app churchSuccTm n) := by
    exact ClosedAt.appClosed ChurchNatRec.church_succ_closed hn
  have hleftCore :
      BetaStarStep
        (Term.app (Term.app church_mul (Term.app churchSuccTm n)) m)
        (Term.app
          (Term.app
            (Term.app (Term.app churchSuccTm n) churchNatTy)
            (Term.app ChurchNatRec.church_add m))
          churchZeroTm) := by
    exact church_mul_apply (Term.app churchSuccTm n) m hSuccN hm
  have hleftIter :
      BetaStarStep
        (Term.app
          (Term.app
            (Term.app (Term.app churchSuccTm n) churchNatTy)
            (Term.app ChurchNatRec.church_add m))
          churchZeroTm)
        target := by
    exact ChurchNatRec.church_succ_iter n churchNatTy
      (Term.app ChurchNatRec.church_add m) churchZeroTm
      hn ChurchNatRec.church_nat_closed
      (ClosedAt.appClosed
        church_add_closed
        hm)
  have hrightArg :
      BetaStarStep
        (Term.app (Term.app church_mul n) m)
        (Term.app
          (Term.app
            (Term.app n churchNatTy)
            (Term.app ChurchNatRec.church_add m))
          churchZeroTm) := by
    exact church_mul_apply n m hn hm
  have hright :
      BetaStarStep
        (Term.app
          (Term.app ChurchNatRec.church_add m)
          (Term.app (Term.app church_mul n) m))
        target := by
    exact betaStarStep_app_right hrightArg
  exact
    Exists.intro target
      (And.intro
        (betaStar_trans hleftCore hleftIter)
        hright)

theorem church_exp_after_n (n : Term) :
    substitute 1 n
      (Term.app
        (Term.app
          (Term.app (Term.var 0) churchNatTy)
          (Term.app church_mul (Term.var 1)))
        churchOneTm) =
      Term.app
        (Term.app
          (Term.app (Term.var 0) churchNatTy)
          (Term.app church_mul n))
        churchOneTm := by
  change
    Term.app
      (Term.app
        (Term.app (substitute 1 n (Term.var 0))
          (substitute 1 n churchNatTy))
        (Term.app (substitute 1 n church_mul)
          (substitute 1 n (Term.var 1))))
      (substitute 1 n churchOneTm) =
      Term.app
        (Term.app
          (Term.app (Term.var 0) churchNatTy)
          (Term.app church_mul n))
        churchOneTm
  rw [substitute_closed 1 n churchNatTy
    (closedAt_zero_at 1 churchNatTy ChurchNatRec.church_nat_closed)]
  rw [substitute_closed 1 n church_mul
    (closedAt_zero_at 1 church_mul church_mul_closed)]
  rw [substitute_closed 1 n churchOneTm
    (closedAt_zero_at 1 churchOneTm church_one_closed)]
  rfl

theorem church_exp_payload (n m : Term)
    (hn : ClosedAt 0 n) :
    substitute 0 m
      (Term.app
        (Term.app
          (Term.app (Term.var 0) churchNatTy)
          (Term.app church_mul n))
        churchOneTm) =
      Term.app
        (Term.app
          (Term.app m churchNatTy)
          (Term.app church_mul n))
        churchOneTm := by
  change
    Term.app
      (Term.app
        (Term.app m (substitute 0 m churchNatTy))
        (Term.app (substitute 0 m church_mul)
          (substitute 0 m n)))
      (substitute 0 m churchOneTm) =
      Term.app
        (Term.app
          (Term.app m churchNatTy)
          (Term.app church_mul n))
        churchOneTm
  rw [substitute_closed 0 m churchNatTy ChurchNatRec.church_nat_closed]
  rw [substitute_closed 0 m church_mul church_mul_closed]
  rw [substitute_closed 0 m n hn]
  rw [substitute_closed 0 m churchOneTm church_one_closed]

theorem church_exp_apply (n m : Term)
    (hn : ClosedAt 0 n) (_hm : ClosedAt 0 m) :
    BetaStarStep
      (Term.app (Term.app church_exp n) m)
      (Term.app
        (Term.app
          (Term.app m churchNatTy)
          (Term.app church_mul n))
        churchOneTm) := by
  unfold church_exp
  apply BetaStarStep.step
  · exact BetaStep.congApp1 _ _ m
      (BetaStep.beta churchNatTy
        (Term.lam churchNatTy
          (Term.app
            (Term.app
              (Term.app (Term.var 0) churchNatTy)
              (Term.app church_mul (Term.var 1)))
            churchOneTm))
        n)
  unfold substitute
  rw [shift_closed 0 n hn]
  rw [substitute_closed 0 n churchNatTy ChurchNatRec.church_nat_closed]
  apply BetaStarStep.step
  · exact BetaStep.beta
      (substitute 0 n churchNatTy)
      (substitute (0 + 1) n
        (Term.app
          (Term.app
            (Term.app (Term.var 0) churchNatTy)
            (Term.app church_mul (Term.var 1)))
          churchOneTm))
      m
  rw [church_exp_after_n n]
  rw [church_exp_payload n m hn]
  exact BetaStarStep.refl
    (Term.app
      (Term.app
        (Term.app m churchNatTy)
        (Term.app church_mul n))
      churchOneTm)

theorem church_exp_zero (n : Term)
    (hn : ClosedAt 0 n) :
    BetaStarStep (Term.app (Term.app church_exp n) churchZeroTm) churchOneTm := by
  exact betaStar_trans
    (church_exp_apply n churchZeroTm hn ChurchNatRec.church_zero_closed)
    (church_zero_apply churchNatTy (Term.app church_mul n) churchOneTm
      ChurchNatRec.church_nat_closed
      (ClosedAt.appClosed church_mul_closed hn)
      church_one_closed)

theorem church_exp_succ_right (n m : Term)
    (hn : ClosedAt 0 n) (hm : ClosedAt 0 m) :
    BetaConv
      (Term.app (Term.app church_exp n) (Term.app churchSuccTm m))
      (Term.app
        (Term.app church_mul n)
        (Term.app (Term.app church_exp n) m)) := by
  let target :=
    Term.app
      (Term.app church_mul n)
      (Term.app
        (Term.app
          (Term.app m churchNatTy)
          (Term.app church_mul n))
        churchOneTm)
  have hSuccM : ClosedAt 0 (Term.app churchSuccTm m) := by
    exact ClosedAt.appClosed ChurchNatRec.church_succ_closed hm
  have hleftCore :
      BetaStarStep
        (Term.app (Term.app church_exp n) (Term.app churchSuccTm m))
        (Term.app
          (Term.app
            (Term.app (Term.app churchSuccTm m) churchNatTy)
            (Term.app church_mul n))
          churchOneTm) := by
    exact church_exp_apply n (Term.app churchSuccTm m) hn hSuccM
  have hleftIter :
      BetaStarStep
        (Term.app
          (Term.app
            (Term.app (Term.app churchSuccTm m) churchNatTy)
            (Term.app church_mul n))
          churchOneTm)
        target := by
    exact ChurchNatRec.church_succ_iter m churchNatTy
      (Term.app church_mul n) churchOneTm
      hm ChurchNatRec.church_nat_closed
      (ClosedAt.appClosed church_mul_closed hn)
  have hrightArg :
      BetaStarStep
        (Term.app (Term.app church_exp n) m)
        (Term.app
          (Term.app
            (Term.app m churchNatTy)
            (Term.app church_mul n))
          churchOneTm) := by
    exact church_exp_apply n m hn hm
  have hright :
      BetaStarStep
        (Term.app
          (Term.app church_mul n)
          (Term.app (Term.app church_exp n) m))
        target := by
    exact betaStarStep_app_right hrightArg
  exact
    Exists.intro target
      (And.intro
        (betaStar_trans hleftCore hleftIter)
        hright)

end BEDC.MetaCIC
