import BEDC.MetaCIC.TypedExamples.ChurchGallery
import BEDC.MetaCIC.TypedExamples.ChurchAlgebra
import BEDC.MetaCIC.Beta.Conversion

namespace BEDC.MetaCIC
namespace ChurchNatRec

abbrev church_succ : Term :=
  churchSuccTm

abbrev church_add : Term :=
  Term.lam churchNatTy
    (Term.lam churchNatTy
      (Term.app
        (Term.app
          (Term.app (Term.var 1) churchNatTy)
          churchSuccTm)
        (Term.var 0)))

abbrev church_add_type_tm : Term :=
  Term.pi churchNatTy (Term.pi churchNatTy churchNatTy)

abbrev app4 (a b c d : Term) : Term :=
  Term.app (Term.app (Term.app a b) c) d

abbrev churchSuccAfterN (n : Term) : Term :=
  Term.lam (Term.pi (Term.var 0) (Term.var 1))
    (Term.lam (Term.var 1)
      (Term.app (Term.var 1)
        (app4 (shift 0 1 (shift 0 1 n))
          (Term.var 2) (Term.var 1) (Term.var 0))))

abbrev churchSuccAfterNX (n X : Term) : Term :=
  Term.lam (Term.pi X X)
    (Term.lam X
      (Term.app (Term.var 1)
        (app4 n X (Term.var 1) (Term.var 0))))

abbrev churchSuccAfterNXF (n X f : Term) : Term :=
  Term.lam X
    (Term.app f (app4 n X f (Term.var 0)))

theorem church_nat_closed :
    ClosedAt 0 churchNatTy := by
  unfold churchNatTy
  apply ClosedAt.piClosed
  · exact ClosedAt.sortClosed
  · apply ClosedAt.piClosed
    · apply ClosedAt.piClosed
      · apply ClosedAt.varClosed
        exact Nat.zero_lt_succ 0
      · apply ClosedAt.varClosed
        exact Nat.lt_succ_self 1
    · apply ClosedAt.piClosed
      · apply ClosedAt.varClosed
        exact Nat.lt_succ_self 1
      · apply ClosedAt.varClosed
        exact Nat.lt_succ_self 2

theorem church_zero_closed :
    ClosedAt 0 churchZeroTm := by
  unfold churchZeroTm
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
      · apply ClosedAt.varClosed
        exact Nat.zero_lt_succ 2

theorem church_succ_closed :
    ClosedAt 0 church_succ := by
  unfold church_succ
  unfold churchSuccTm
  apply ClosedAt.lamClosed
  · exact church_nat_closed
  · apply ClosedAt.lamClosed
    · exact ClosedAt.sortClosed
    · apply ClosedAt.lamClosed
      · apply ClosedAt.piClosed
        · apply ClosedAt.varClosed
          exact Nat.zero_lt_succ 1
        · apply ClosedAt.varClosed
          exact Nat.succ_lt_succ (Nat.zero_lt_succ 1)
      · apply ClosedAt.lamClosed
        · apply ClosedAt.varClosed
          exact Nat.succ_lt_succ (Nat.zero_lt_succ 1)
        · apply ClosedAt.appClosed
          · apply ClosedAt.varClosed
            exact Nat.succ_lt_succ (Nat.zero_lt_succ 2)
          · apply ClosedAt.appClosed
            · apply ClosedAt.appClosed
              · apply ClosedAt.appClosed
                · apply ClosedAt.varClosed
                  exact Nat.lt_succ_self 3
                · apply ClosedAt.varClosed
                  exact Nat.succ_lt_succ
                    (Nat.succ_lt_succ (Nat.zero_lt_succ 1))
              · apply ClosedAt.varClosed
                exact Nat.succ_lt_succ (Nat.zero_lt_succ 2)
            · apply ClosedAt.varClosed
              exact Nat.zero_lt_succ 3

theorem church_nat_type_in_two_ctx :
    HasType [churchNatTy, churchNatTy] churchNatTy Term.sort := by
  apply HasType.piRule
  · exact HasType.sortRule [churchNatTy, churchNatTy]
  · apply HasType.piRule
    · apply HasType.piRule
      · apply HasType.varRule
        rfl
      · apply HasType.varRule
        rfl
    · apply HasType.piRule
      · apply HasType.varRule
        rfl
      · apply HasType.varRule
        rfl

theorem church_succ_payload_after_X (n X : Term)
    (hn : ClosedAt 0 n) :
    substitute 2 X (app4 n (Term.var 2) (Term.var 1) (Term.var 0)) =
      app4 n X (Term.var 1) (Term.var 0) := by
  unfold app4
  change
    Term.app
      (Term.app
        (Term.app (substitute 2 X n) X)
        (Term.var 1))
      (Term.var 0) =
    Term.app (Term.app (Term.app n X) (Term.var 1)) (Term.var 0)
  rw [substitute_closed 2 X n (closedAt_zero_at 2 n hn)]

theorem church_succ_payload_after_f (n X f : Term)
    (hn : ClosedAt 0 n) (hX : ClosedAt 0 X) :
    substitute 1 f (app4 n X (Term.var 1) (Term.var 0)) =
      app4 n X f (Term.var 0) := by
  unfold app4
  change
    Term.app
      (Term.app
        (Term.app (substitute 1 f n) (substitute 1 f X))
        f)
      (Term.var 0) =
    Term.app (Term.app (Term.app n X) f) (Term.var 0)
  rw [substitute_closed 1 f n (closedAt_zero_at 1 n hn)]
  rw [substitute_closed 1 f X (closedAt_zero_at 1 X hX)]

theorem church_succ_payload_after_x (n X f x : Term)
    (hn : ClosedAt 0 n) (hX : ClosedAt 0 X) (hf : ClosedAt 0 f) :
    substitute 0 x (Term.app f (app4 n X f (Term.var 0))) =
      Term.app f (app4 n X f x) := by
  unfold app4
  change
    Term.app (substitute 0 x f)
      (substitute 0 x
        (Term.app (Term.app (Term.app n X) f) (Term.var 0))) =
    Term.app f (Term.app (Term.app (Term.app n X) f) x)
  rw [substitute_closed 0 x f hf]
  change
    Term.app f
      (Term.app (substitute 0 x (Term.app (Term.app n X) f)) x) =
    Term.app f (Term.app (Term.app (Term.app n X) f) x)
  change
    Term.app f
      (Term.app
        (Term.app (substitute 0 x (Term.app n X))
          (substitute 0 x f))
        x) =
    Term.app f (Term.app (Term.app (Term.app n X) f) x)
  rw [substitute_closed 0 x f hf]
  change
    Term.app f
      (Term.app
        (Term.app
          (Term.app (substitute 0 x n) (substitute 0 x X))
          f)
        x) =
    Term.app f (Term.app (Term.app (Term.app n X) f) x)
  rw [substitute_closed 0 x n hn]
  rw [substitute_closed 0 x X hX]

theorem church_succ_after_X (n X : Term)
    (hn : ClosedAt 0 n) (hX : ClosedAt 0 X) :
    substitute 0 X (churchSuccAfterN n) = churchSuccAfterNX n X := by
  unfold churchSuccAfterN churchSuccAfterNX app4
  change
    Term.lam (substitute 0 X (Term.pi (Term.var 0) (Term.var 1)))
      (substitute 1 (shift 0 1 X)
        (Term.lam (Term.var 1)
          (Term.app (Term.var 1)
            (Term.app
              (Term.app
                (Term.app (shift 0 1 (shift 0 1 n)) (Term.var 2))
                (Term.var 1))
              (Term.var 0))))) =
    Term.lam (Term.pi X X)
      (Term.lam X
        (Term.app (Term.var 1)
          (Term.app
            (Term.app (Term.app n X) (Term.var 1))
            (Term.var 0))))
  rw [show substitute 0 X (Term.pi (Term.var 0) (Term.var 1)) =
    Term.pi X (shift 0 1 X) by rfl]
  rw [shift_closed 0 X hX]
  change
    Term.lam (Term.pi X X)
      (Term.lam (substitute 1 X (Term.var 1))
        (substitute 2 (shift 0 1 X)
          (Term.app (Term.var 1)
            (Term.app
              (Term.app
                (Term.app (shift 0 1 (shift 0 1 n)) (Term.var 2))
                (Term.var 1))
              (Term.var 0))))) =
    Term.lam (Term.pi X X)
      (Term.lam X
        (Term.app (Term.var 1)
          (Term.app
            (Term.app (Term.app n X) (Term.var 1))
            (Term.var 0))))
  rw [shift_closed 0 X hX]
  rw [shift_closed 0 n hn]
  rw [shift_closed 0 n hn]
  change
    Term.lam (Term.pi X X)
      (Term.lam X
        (Term.app (Term.var 1)
          (substitute 2 X
            (Term.app
              (Term.app (Term.app n (Term.var 2)) (Term.var 1))
              (Term.var 0))))) =
    Term.lam (Term.pi X X)
      (Term.lam X
        (Term.app (Term.var 1)
          (Term.app
            (Term.app (Term.app n X) (Term.var 1))
            (Term.var 0))))
  rw [church_succ_payload_after_X n X hn]

theorem church_succ_after_f (n X f : Term)
    (hn : ClosedAt 0 n) (hX : ClosedAt 0 X) (hf : ClosedAt 0 f) :
    substitute 0 f (Term.lam X
      (Term.app (Term.var 1) (app4 n X (Term.var 1) (Term.var 0)))) =
      churchSuccAfterNXF n X f := by
  unfold churchSuccAfterNXF app4
  change
    Term.lam (substitute 0 f X)
      (substitute 1 (shift 0 1 f)
        (Term.app (Term.var 1)
          (Term.app
            (Term.app (Term.app n X) (Term.var 1))
            (Term.var 0)))) =
    Term.lam X
      (Term.app f
        (Term.app (Term.app (Term.app n X) f) (Term.var 0)))
  rw [substitute_closed 0 f X hX]
  rw [shift_closed 0 f hf]
  change
    Term.lam X
      (Term.app f
        (substitute 1 f
          (Term.app
            (Term.app (Term.app n X) (Term.var 1))
          (Term.var 0)))) =
    Term.lam X
      (Term.app f
        (Term.app (Term.app (Term.app n X) f) (Term.var 0)))
  rw [church_succ_payload_after_f n X f hn hX]

theorem church_add_payload (n m : Term)
    (hn : ClosedAt 0 n) :
    substitute 0 m
      (Term.app
        (Term.app (Term.app n churchNatTy) churchSuccTm)
        (Term.var 0)) =
      Term.app (Term.app (Term.app n churchNatTy) churchSuccTm) m := by
  change
    Term.app
      (substitute 0 m
        (Term.app (Term.app n churchNatTy) churchSuccTm))
      m =
    Term.app (Term.app (Term.app n churchNatTy) churchSuccTm) m
  change
    Term.app
      (Term.app
        (substitute 0 m (Term.app n churchNatTy))
        (substitute 0 m churchSuccTm))
      m =
    Term.app (Term.app (Term.app n churchNatTy) churchSuccTm) m
  rw [substitute_closed 0 m churchSuccTm church_succ_closed]
  change
    Term.app
      (Term.app
        (Term.app (substitute 0 m n) (substitute 0 m churchNatTy))
        churchSuccTm)
      m =
    Term.app (Term.app (Term.app n churchNatTy) churchSuccTm) m
  rw [substitute_closed 0 m n hn]
  rw [substitute_closed 0 m churchNatTy church_nat_closed]

theorem church_add_after_n (n : Term)
    (_hn : ClosedAt 0 n) :
    substitute 1 n
      (Term.app
        (Term.app (Term.app (Term.var 1) churchNatTy) churchSuccTm)
        (Term.var 0)) =
      Term.app
        (Term.app (Term.app n churchNatTy) churchSuccTm)
        (Term.var 0) := by
  change
    Term.app
      (Term.app
        (Term.app (substitute 1 n (Term.var 1))
          (substitute 1 n churchNatTy))
        (substitute 1 n churchSuccTm))
      (Term.var 0) =
    Term.app
      (Term.app (Term.app n churchNatTy) churchSuccTm)
      (Term.var 0)
  rw [substitute_closed 1 n churchNatTy
    (closedAt_zero_at 1 churchNatTy church_nat_closed)]
  rw [substitute_closed 1 n churchSuccTm
    (closedAt_zero_at 1 churchSuccTm church_succ_closed)]
  change
    Term.app
      (Term.app
        (Term.app n churchNatTy)
        churchSuccTm)
      (Term.var 0) =
    Term.app
      (Term.app (Term.app n churchNatTy) churchSuccTm)
      (Term.var 0)
  rfl

theorem church_succ_iter (n X f x : Term)
    (hn : ClosedAt 0 n) (hX : ClosedAt 0 X) (hf : ClosedAt 0 f) :
    BetaStarStep
      (Term.app (Term.app (Term.app (Term.app church_succ n) X) f) x)
      (Term.app f (Term.app (Term.app (Term.app n X) f) x)) := by
  unfold church_succ
  unfold churchSuccTm
  apply BetaStarStep.step
  · exact BetaStep.congApp1 _ _ x
      (BetaStep.congApp1 _ _ f
        (BetaStep.congApp1 _ _ X
          (BetaStep.beta churchNatTy
            (Term.lam Term.sort
              (Term.lam (Term.pi (Term.var 0) (Term.var 1))
                (Term.lam (Term.var 1)
                  (Term.app (Term.var 1)
                    (Term.app
                      (Term.app
                        (Term.app (Term.var 3) (Term.var 2))
                        (Term.var 1))
                      (Term.var 0))))))
            n)))
  unfold substitute
  rw [shift_closed 0 n hn]
  change
    BetaStarStep
      (app4 (Term.lam Term.sort (churchSuccAfterN n)) X f x)
      (Term.app f (app4 n X f x))
  apply BetaStarStep.step
  · exact BetaStep.congApp1 _ _ x
      (BetaStep.congApp1 _ _ f
        (BetaStep.beta
          (substitute 0 n Term.sort)
          (churchSuccAfterN n)
          X))
  rw [church_succ_after_X n X hn hX]
  change
    BetaStarStep
      (Term.app
        (Term.app
          (Term.lam (Term.pi X X)
            (Term.lam X
              (Term.app (Term.var 1)
                (app4 n X (Term.var 1) (Term.var 0)))))
          f)
        x)
      (Term.app f (Term.app (Term.app (Term.app n X) f) x))
  apply BetaStarStep.step
  · exact BetaStep.congApp1 _ _ x
      (BetaStep.beta
        (Term.pi X X)
        (Term.lam X
          (Term.app (Term.var 1)
            (app4 n X (Term.var 1) (Term.var 0))))
        f)
  rw [church_succ_after_f n X f hn hX hf]
  change
    BetaStarStep
      (Term.app
        (Term.lam X
          (Term.app f (app4 n X f (Term.var 0))))
        x)
      (Term.app f (Term.app (Term.app (Term.app n X) f) x))
  apply BetaStarStep.step
  · exact BetaStep.beta X
      (Term.app f (app4 n X f (Term.var 0)))
      x
  change
    BetaStarStep
      (substitute 0 x (Term.app f (app4 n X f (Term.var 0))))
      (Term.app f (Term.app (Term.app (Term.app n X) f) x))
  rw [church_succ_payload_after_x n X f x hn hX hf]
  exact BetaStarStep.refl (Term.app f (app4 n X f x))

theorem church_succ_zero_conv (X f x : Term)
    (hX : ClosedAt 0 X) (hf : ClosedAt 0 f) (hx : ClosedAt 0 x) :
    BetaConv
      (Term.app (Term.app (Term.app (Term.app church_succ churchZeroTm) X) f) x)
      (Term.app f x) := by
  exact BetaConv.of_betaStar_left
    (betaStar_trans
      (church_succ_iter churchZeroTm X f x church_zero_closed hX hf)
      (betaStarStep_app_right
        (church_zero_apply X f x hX hf hx)))

theorem church_succ_zero_to_one (X f x : Term)
    (hX : ClosedAt 0 X) (hf : ClosedAt 0 f) (hx : ClosedAt 0 x) :
    BetaConv
      (Term.app (Term.app (Term.app (Term.app church_succ churchZeroTm) X) f) x)
      (Term.app (Term.app (Term.app churchOneTm X) f) x) := by
  exact
    Exists.intro (Term.app f x)
      (And.intro
        (betaStar_trans
          (church_succ_iter churchZeroTm X f x church_zero_closed hX hf)
          (betaStarStep_app_right
            (church_zero_apply X f x hX hf hx)))
        (church_one_apply X f x hX hf hx))

theorem church_add_zero (m : Term)
    (hm : ClosedAt 0 m) :
    BetaStarStep (Term.app (Term.app church_add churchZeroTm) m) m := by
  unfold church_add
  apply BetaStarStep.step
  · exact BetaStep.congApp1 _ _ m
      (BetaStep.beta churchNatTy
        (Term.lam churchNatTy
          (Term.app
            (Term.app
              (Term.app (Term.var 1) churchNatTy)
              churchSuccTm)
            (Term.var 0)))
        churchZeroTm)
  unfold substitute
  rw [shift_closed 0 churchZeroTm church_zero_closed]
  rw [substitute_closed 0 churchZeroTm churchNatTy church_nat_closed]
  change
    BetaStarStep
      (Term.app
        (Term.lam churchNatTy
          (Term.app
            (Term.app
              (Term.app (shift 0 1 churchZeroTm) churchNatTy)
              churchSuccTm)
            (Term.var 0)))
        m)
      m
  apply BetaStarStep.step
  · exact BetaStep.beta churchNatTy
      (Term.app
        (Term.app
          (Term.app (shift 0 1 churchZeroTm) churchNatTy)
          churchSuccTm)
        (Term.var 0))
      m
  rw [shift_closed 0 churchZeroTm church_zero_closed]
  rw [church_add_payload churchZeroTm m church_zero_closed]
  exact church_zero_apply churchNatTy churchSuccTm m
    church_nat_closed church_succ_closed hm

theorem church_add_apply (n m : Term)
    (hn : ClosedAt 0 n) (_hm : ClosedAt 0 m) :
    BetaStarStep
      (Term.app (Term.app church_add n) m)
      (Term.app (Term.app (Term.app n churchNatTy) churchSuccTm) m) := by
  unfold church_add
  apply BetaStarStep.step
  · exact BetaStep.congApp1 _ _ m
      (BetaStep.beta churchNatTy
        (Term.lam churchNatTy
          (Term.app
            (Term.app
              (Term.app (Term.var 1) churchNatTy)
              churchSuccTm)
            (Term.var 0)))
        n)
  unfold substitute
  rw [shift_closed 0 n hn]
  rw [substitute_closed 0 n churchNatTy church_nat_closed]
  apply BetaStarStep.step
  · exact BetaStep.beta
      (substitute 0 n churchNatTy)
      (substitute (0 + 1) n
        (Term.app
          (Term.app
            (Term.app (Term.var 1) churchNatTy)
            churchSuccTm)
          (Term.var 0)))
      m
  rw [church_add_after_n n hn]
  rw [church_add_payload n m hn]
  exact BetaStarStep.refl
    (Term.app (Term.app (Term.app n churchNatTy) churchSuccTm) m)

theorem church_add_succ_left (n m : Term)
    (hn : ClosedAt 0 n) (hm : ClosedAt 0 m) :
    BetaConv
      (Term.app (Term.app church_add (Term.app church_succ n)) m)
      (Term.app church_succ (Term.app (Term.app church_add n) m)) := by
  let target :=
    Term.app churchSuccTm
      (Term.app (Term.app (Term.app n churchNatTy) churchSuccTm) m)
  have hSuccN : ClosedAt 0 (Term.app church_succ n) := by
    apply ClosedAt.appClosed
    · exact church_succ_closed
    · exact hn
  have hleftCore :
      BetaStarStep
        (Term.app (Term.app church_add (Term.app church_succ n)) m)
        (Term.app
          (Term.app
            (Term.app (Term.app church_succ n) churchNatTy)
            churchSuccTm)
          m) := by
    exact church_add_apply (Term.app church_succ n) m hSuccN hm
  have hleftIter :
      BetaStarStep
        (Term.app
          (Term.app
            (Term.app (Term.app church_succ n) churchNatTy)
            churchSuccTm)
          m)
        target := by
    exact church_succ_iter n churchNatTy churchSuccTm m
      hn church_nat_closed church_succ_closed
  have hrightArg :
      BetaStarStep
        (Term.app (Term.app church_add n) m)
        (Term.app (Term.app (Term.app n churchNatTy) churchSuccTm) m) := by
    exact church_add_apply n m hn hm
  have hright :
      BetaStarStep
        (Term.app church_succ (Term.app (Term.app church_add n) m))
        target := by
    exact betaStarStep_app_right hrightArg
  exact
    Exists.intro target
      (And.intro
        (betaStar_trans hleftCore hleftIter)
        hright)

end ChurchNatRec
end BEDC.MetaCIC
