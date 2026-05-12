import BEDC.MetaCIC.Typing

namespace BEDC.MetaCIC

abbrev churchBoolTy : Term :=
  Term.pi Term.sort
    (Term.pi (Term.var 0)
      (Term.pi (Term.var 1) (Term.var 2)))

abbrev churchTrueTm : Term :=
  Term.lam Term.sort
    (Term.lam (Term.var 0)
      (Term.lam (Term.var 1) (Term.var 1)))

abbrev churchFalseTm : Term :=
  Term.lam Term.sort
    (Term.lam (Term.var 0)
      (Term.lam (Term.var 1) (Term.var 0)))

abbrev churchNatTy : Term :=
  Term.pi Term.sort
    (Term.pi (Term.pi (Term.var 0) (Term.var 1))
      (Term.pi (Term.var 1) (Term.var 2)))

abbrev churchZeroTm : Term :=
  Term.lam Term.sort
    (Term.lam (Term.pi (Term.var 0) (Term.var 1))
      (Term.lam (Term.var 1) (Term.var 0)))

abbrev churchOneTm : Term :=
  Term.lam Term.sort
    (Term.lam (Term.pi (Term.var 0) (Term.var 1))
      (Term.lam (Term.var 1)
        (Term.app (Term.var 1) (Term.var 0))))

abbrev churchSuccTy : Term :=
  Term.pi churchNatTy churchNatTy

abbrev churchSuccTm : Term :=
  Term.lam churchNatTy
    (Term.lam Term.sort
      (Term.lam (Term.pi (Term.var 0) (Term.var 1))
        (Term.lam (Term.var 1)
          (Term.app (Term.var 1)
            (Term.app
              (Term.app
                (Term.app (Term.var 3) (Term.var 2))
                (Term.var 1))
              (Term.var 0))))))

abbrev churchIdentityTy : Term :=
  Term.pi Term.sort (Term.pi (Term.var 0) (Term.var 1))

abbrev churchIdentityTm : Term :=
  Term.lam Term.sort (Term.lam (Term.var 0) (Term.var 0))

abbrev churchConstTy : Term :=
  Term.pi Term.sort
    (Term.pi Term.sort
      (Term.pi (Term.var 1)
        (Term.pi (Term.var 1) (Term.var 3))))

abbrev churchConstTm : Term :=
  Term.lam Term.sort
    (Term.lam Term.sort
      (Term.lam (Term.var 1)
        (Term.lam (Term.var 1) (Term.var 1))))

theorem church_bool_type :
    HasType [] churchBoolTy Term.sort := by
  apply HasType.piRule
  · exact HasType.sortRule []
  · apply HasType.piRule
    · apply HasType.varRule
      rfl
    · apply HasType.piRule
      · apply HasType.varRule
        rfl
      · apply HasType.varRule
        rfl

theorem church_true :
    HasType [] churchTrueTm churchBoolTy := by
  apply HasType.lamRule
  · exact HasType.sortRule []
  · apply HasType.lamRule
    · apply HasType.varRule
      rfl
    · apply HasType.lamRule
      · apply HasType.varRule
        rfl
      · apply HasType.varRule
        rfl

theorem church_false :
    HasType [] churchFalseTm churchBoolTy := by
  apply HasType.lamRule
  · exact HasType.sortRule []
  · apply HasType.lamRule
    · apply HasType.varRule
      rfl
    · apply HasType.lamRule
      · apply HasType.varRule
        rfl
      · apply HasType.varRule
        rfl

theorem church_nat_type :
    HasType [] churchNatTy Term.sort := by
  apply HasType.piRule
  · exact HasType.sortRule []
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

theorem church_zero :
    HasType [] churchZeroTm churchNatTy := by
  apply HasType.lamRule
  · exact HasType.sortRule []
  · apply HasType.lamRule
    · apply HasType.piRule
      · apply HasType.varRule
        rfl
      · apply HasType.varRule
        rfl
    · apply HasType.lamRule
      · apply HasType.varRule
        rfl
      · apply HasType.varRule
        rfl

theorem church_one :
    HasType [] churchOneTm churchNatTy := by
  apply HasType.lamRule
  · exact HasType.sortRule []
  · apply HasType.lamRule
    · apply HasType.piRule
      · apply HasType.varRule
        rfl
      · apply HasType.varRule
        rfl
    · apply HasType.lamRule
      · apply HasType.varRule
        rfl
      · exact HasType.appRule
          [Term.var 2,
            Term.pi (Term.var 1) (Term.var 2),
            Term.sort]
          (Term.var 1)
          (Term.var 0)
          (Term.var 2)
          (Term.var 3)
          (HasType.varRule
            [Term.var 2,
              Term.pi (Term.var 1) (Term.var 2),
              Term.sort]
            1
            (Term.pi (Term.var 2) (Term.var 3))
            rfl)
          (HasType.varRule
            [Term.var 2,
              Term.pi (Term.var 1) (Term.var 2),
              Term.sort]
            0
            (Term.var 2)
            rfl)

theorem church_nat_type_in_ctx :
    HasType [churchNatTy] churchNatTy Term.sort := by
  apply HasType.piRule
  · exact HasType.sortRule [churchNatTy]
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

theorem church_succ_type :
    HasType [] churchSuccTy Term.sort := by
  apply HasType.piRule
  · exact church_nat_type
  · exact church_nat_type_in_ctx

theorem church_succ :
    HasType [] churchSuccTm churchSuccTy := by
  apply HasType.lamRule
  · exact church_nat_type
  · apply HasType.lamRule
    · exact HasType.sortRule [churchNatTy]
    · apply HasType.lamRule
      · apply HasType.piRule
        · apply HasType.varRule
          rfl
        · apply HasType.varRule
          rfl
      · apply HasType.lamRule
        · apply HasType.varRule
          rfl
        · exact HasType.appRule
            [Term.var 2,
              Term.pi (Term.var 1) (Term.var 2),
              Term.sort,
              churchNatTy]
            (Term.var 1)
            (Term.app
              (Term.app
                (Term.app (Term.var 3) (Term.var 2))
                (Term.var 1))
              (Term.var 0))
            (Term.var 2)
            (Term.var 3)
            (HasType.varRule
              [Term.var 2,
                Term.pi (Term.var 1) (Term.var 2),
                Term.sort,
                churchNatTy]
              1
              (Term.pi (Term.var 2) (Term.var 3))
              rfl)
            (HasType.appRule
              [Term.var 2,
                Term.pi (Term.var 1) (Term.var 2),
                Term.sort,
                churchNatTy]
              (Term.app
                (Term.app (Term.var 3) (Term.var 2))
                (Term.var 1))
              (Term.var 0)
              (Term.var 2)
              (Term.var 3)
              (HasType.appRule
                [Term.var 2,
                  Term.pi (Term.var 1) (Term.var 2),
                  Term.sort,
                  churchNatTy]
                (Term.app (Term.var 3) (Term.var 2))
                (Term.var 1)
                (Term.pi (Term.var 2) (Term.var 3))
                (Term.pi (Term.var 3) (Term.var 4))
                (HasType.appRule
                  [Term.var 2,
                    Term.pi (Term.var 1) (Term.var 2),
                    Term.sort,
                    churchNatTy]
                  (Term.var 3)
                  (Term.var 2)
                  Term.sort
                  (Term.pi
                    (Term.pi (Term.var 0) (Term.var 1))
                    (Term.pi (Term.var 1) (Term.var 2)))
                  (HasType.varRule
                    [Term.var 2,
                      Term.pi (Term.var 1) (Term.var 2),
                      Term.sort,
                      churchNatTy]
                    3
                    churchNatTy
                    rfl)
                  (HasType.varRule
                    [Term.var 2,
                      Term.pi (Term.var 1) (Term.var 2),
                      Term.sort,
                      churchNatTy]
                    2
                    Term.sort
                    rfl))
                (HasType.varRule
                  [Term.var 2,
                    Term.pi (Term.var 1) (Term.var 2),
                    Term.sort,
                    churchNatTy]
                  1
                  (Term.pi (Term.var 2) (Term.var 3))
                  rfl))
              (HasType.varRule
                [Term.var 2,
                  Term.pi (Term.var 1) (Term.var 2),
                  Term.sort,
                  churchNatTy]
                0
                (Term.var 2)
                rfl))

theorem church_identity_type :
    HasType [] churchIdentityTy Term.sort := by
  apply HasType.piRule
  · exact HasType.sortRule []
  · apply HasType.piRule
    · apply HasType.varRule
      rfl
    · apply HasType.varRule
      rfl

theorem church_identity :
    HasType [] churchIdentityTm churchIdentityTy := by
  apply HasType.lamRule
  · exact HasType.sortRule []
  · apply HasType.lamRule
    · apply HasType.varRule
      rfl
    · apply HasType.varRule
      rfl

theorem church_const_type :
    HasType [] churchConstTy Term.sort := by
  apply HasType.piRule
  · exact HasType.sortRule []
  · apply HasType.piRule
    · exact HasType.sortRule [Term.sort]
    · apply HasType.piRule
      · apply HasType.varRule
        rfl
      · apply HasType.piRule
        · apply HasType.varRule
          rfl
        · apply HasType.varRule
          rfl

theorem church_const :
    HasType [] churchConstTm churchConstTy := by
  apply HasType.lamRule
  · exact HasType.sortRule []
  · apply HasType.lamRule
    · exact HasType.sortRule [Term.sort]
    · apply HasType.lamRule
      · apply HasType.varRule
        rfl
      · apply HasType.lamRule
        · apply HasType.varRule
          rfl
        · apply HasType.varRule
          rfl

theorem church_bool_elim_sort :
    HasType []
      (Term.app
        (Term.app
          (Term.app churchTrueTm Term.sort)
          Term.sort)
        Term.sort)
      Term.sort := by
  exact HasType.appRule []
    (Term.app
      (Term.app churchTrueTm Term.sort)
      Term.sort)
    Term.sort
    Term.sort
    Term.sort
    (HasType.appRule []
      (Term.app churchTrueTm Term.sort)
      Term.sort
      Term.sort
      (Term.pi Term.sort Term.sort)
      (HasType.appRule []
        churchTrueTm
        Term.sort
        Term.sort
        (Term.pi (Term.var 0)
          (Term.pi (Term.var 1) (Term.var 2)))
        church_true
        (HasType.sortRule []))
      (HasType.sortRule []))
    (HasType.sortRule [])

end BEDC.MetaCIC
