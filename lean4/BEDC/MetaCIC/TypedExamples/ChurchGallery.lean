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

abbrev churchPairTy : Term :=
  Term.pi Term.sort
    (Term.pi Term.sort
      (Term.pi Term.sort
        (Term.pi
          (Term.pi (Term.var 2)
            (Term.pi (Term.var 2) (Term.var 2)))
          (Term.var 1))))

abbrev churchPairABTy : Term :=
  Term.pi Term.sort
    (Term.pi
      (Term.pi (Term.var 2)
        (Term.pi (Term.var 2) (Term.var 2)))
      (Term.var 1))

abbrev churchMkPairTy : Term :=
  Term.pi Term.sort
    (Term.pi Term.sort
      (Term.pi (Term.var 1)
        (Term.pi (Term.var 1)
          (Term.pi Term.sort
            (Term.pi
              (Term.pi (Term.var 4)
                (Term.pi (Term.var 4) (Term.var 2)))
              (Term.var 1))))))

abbrev churchMkPairTm : Term :=
  Term.lam Term.sort
    (Term.lam Term.sort
      (Term.lam (Term.var 1)
        (Term.lam (Term.var 1)
          (Term.lam Term.sort
            (Term.lam
              (Term.pi (Term.var 4)
                (Term.pi (Term.var 4) (Term.var 2)))
              (Term.app
                (Term.app (Term.var 0) (Term.var 3))
                (Term.var 2)))))))

abbrev churchFstTy : Term :=
  Term.pi Term.sort
    (Term.pi Term.sort
      (Term.pi churchPairABTy (Term.var 2)))

abbrev churchFstTm : Term :=
  Term.lam Term.sort
    (Term.lam Term.sort
      (Term.lam churchPairABTy
        (Term.app
          (Term.app (Term.var 0) (Term.var 2))
          (Term.lam (Term.var 2)
            (Term.lam (Term.var 2) (Term.var 1))))))

abbrev churchSndTy : Term :=
  Term.pi Term.sort
    (Term.pi Term.sort
      (Term.pi churchPairABTy (Term.var 1)))

abbrev churchSndTm : Term :=
  Term.lam Term.sort
    (Term.lam Term.sort
      (Term.lam churchPairABTy
        (Term.app
          (Term.app (Term.var 0) (Term.var 1))
          (Term.lam (Term.var 2)
            (Term.lam (Term.var 2) (Term.var 0))))))

abbrev churchPairFormerTm : Term :=
  Term.lam Term.sort
    (Term.lam Term.sort churchPairABTy)

abbrev churchPairFormerTy : Term :=
  Term.pi Term.sort (Term.pi Term.sort Term.sort)

theorem church_pair_type :
    HasType [] churchPairTy Term.sort := by
  apply HasType.piRule
  · exact HasType.sortRule []
  · apply HasType.piRule
    · exact HasType.sortRule [Term.sort]
    · apply HasType.piRule
      · exact HasType.sortRule [Term.sort, Term.sort]
      · apply HasType.piRule
        · apply HasType.piRule
          · apply HasType.varRule
            rfl
          · apply HasType.piRule
            · apply HasType.varRule
              rfl
            · apply HasType.varRule
              rfl
        · apply HasType.varRule
          rfl

theorem church_pair_ab_type :
    HasType [Term.sort, Term.sort] churchPairABTy Term.sort := by
  apply HasType.piRule
  · exact HasType.sortRule [Term.sort, Term.sort]
  · apply HasType.piRule
    · apply HasType.piRule
      · apply HasType.varRule
        rfl
      · apply HasType.piRule
        · apply HasType.varRule
          rfl
        · apply HasType.varRule
          rfl
    · apply HasType.varRule
      rfl

theorem church_mk_pair_type :
    HasType [] churchMkPairTy Term.sort := by
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
        · apply HasType.piRule
          · exact HasType.sortRule [Term.var 2, Term.var 2, Term.sort, Term.sort]
          · apply HasType.piRule
            · apply HasType.piRule
              · apply HasType.varRule
                rfl
              · apply HasType.piRule
                · apply HasType.varRule
                  rfl
                · apply HasType.varRule
                  rfl
            · apply HasType.varRule
              rfl

theorem church_mk_pair :
    HasType [] churchMkPairTm churchMkPairTy := by
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
        · apply HasType.lamRule
          · exact HasType.sortRule [Term.var 2, Term.var 2, Term.sort, Term.sort]
          · apply HasType.lamRule
            · apply HasType.piRule
              · apply HasType.varRule
                rfl
              · apply HasType.piRule
                · apply HasType.varRule
                  rfl
                · apply HasType.varRule
                  rfl
            · exact HasType.appRule
                [Term.pi (Term.var 5) (Term.pi (Term.var 5) (Term.var 3)),
                  Term.sort,
                  Term.var 2,
                  Term.var 2,
                  Term.sort,
                  Term.sort]
                (Term.app (Term.var 0) (Term.var 3))
                (Term.var 2)
                (Term.var 4)
                (Term.var 2)
                (HasType.appRule
                  [Term.pi (Term.var 5) (Term.pi (Term.var 5) (Term.var 3)),
                    Term.sort,
                    Term.var 2,
                    Term.var 2,
                    Term.sort,
                    Term.sort]
                  (Term.var 0)
                  (Term.var 3)
                  (Term.var 5)
                  (Term.pi (Term.var 5) (Term.var 3))
                  (HasType.varRule
                    [Term.pi (Term.var 5) (Term.pi (Term.var 5) (Term.var 3)),
                      Term.sort,
                      Term.var 2,
                      Term.var 2,
                      Term.sort,
                      Term.sort]
                    0
                    (Term.pi (Term.var 5)
                      (Term.pi (Term.var 5) (Term.var 3)))
                    rfl)
                  (HasType.varRule
                    [Term.pi (Term.var 5) (Term.pi (Term.var 5) (Term.var 3)),
                      Term.sort,
                      Term.var 2,
                      Term.var 2,
                      Term.sort,
                      Term.sort]
                    3
                    (Term.var 5)
                    rfl))
                (HasType.varRule
                  [Term.pi (Term.var 5) (Term.pi (Term.var 5) (Term.var 3)),
                    Term.sort,
                    Term.var 2,
                    Term.var 2,
                    Term.sort,
                    Term.sort]
                  2
                  (Term.var 4)
                  rfl)

theorem church_fst_type :
    HasType [] churchFstTy Term.sort := by
  apply HasType.piRule
  · exact HasType.sortRule []
  · apply HasType.piRule
    · exact HasType.sortRule [Term.sort]
    · apply HasType.piRule
      · exact church_pair_ab_type
      · apply HasType.varRule
        rfl

theorem church_fst :
    HasType [] churchFstTm churchFstTy := by
  apply HasType.lamRule
  · exact HasType.sortRule []
  · apply HasType.lamRule
    · exact HasType.sortRule [Term.sort]
    · apply HasType.lamRule
      · exact church_pair_ab_type
      · exact HasType.appRule
          [shift 0 1 churchPairABTy, Term.sort, Term.sort]
          (Term.app (Term.var 0) (Term.var 2))
          (Term.lam (Term.var 2) (Term.lam (Term.var 2) (Term.var 1)))
          (Term.pi (Term.var 2) (Term.pi (Term.var 2) (Term.var 4)))
          (Term.var 3)
          (HasType.appRule
            [shift 0 1 churchPairABTy, Term.sort, Term.sort]
            (Term.var 0)
            (Term.var 2)
            Term.sort
            (Term.pi
              (Term.pi (Term.var 3)
                (Term.pi (Term.var 3) (Term.var 2)))
              (Term.var 1))
            (HasType.varRule
              [shift 0 1 churchPairABTy, Term.sort, Term.sort]
              0
              (Term.pi Term.sort
                (Term.pi
                  (Term.pi (Term.var 3)
                    (Term.pi (Term.var 3) (Term.var 2)))
                  (Term.var 1)))
              rfl)
            (HasType.varRule
              [shift 0 1 churchPairABTy, Term.sort, Term.sort]
              2
              Term.sort
              rfl))
          (HasType.lamRule
            [shift 0 1 churchPairABTy, Term.sort, Term.sort]
            (Term.var 2)
            (Term.lam (Term.var 2) (Term.var 1))
            (Term.pi (Term.var 2) (Term.var 4))
            (HasType.varRule
              [shift 0 1 churchPairABTy, Term.sort, Term.sort]
              2
              Term.sort
              rfl)
            (HasType.lamRule
              [Term.var 3, shift 0 1 churchPairABTy, Term.sort, Term.sort]
              (Term.var 2)
              (Term.var 1)
              (Term.var 4)
              (HasType.varRule
                [Term.var 3, shift 0 1 churchPairABTy, Term.sort, Term.sort]
                2
                Term.sort
                rfl)
              (HasType.varRule
                [Term.var 3, Term.var 3, shift 0 1 churchPairABTy, Term.sort, Term.sort]
                1
                (Term.var 4)
                rfl)))

theorem church_snd_type :
    HasType [] churchSndTy Term.sort := by
  apply HasType.piRule
  · exact HasType.sortRule []
  · apply HasType.piRule
    · exact HasType.sortRule [Term.sort]
    · apply HasType.piRule
      · exact church_pair_ab_type
      · apply HasType.varRule
        rfl

theorem church_snc_type :
    HasType [] churchSndTy Term.sort := by
  exact church_snd_type

theorem church_snd :
    HasType [] churchSndTm churchSndTy := by
  apply HasType.lamRule
  · exact HasType.sortRule []
  · apply HasType.lamRule
    · exact HasType.sortRule [Term.sort]
    · apply HasType.lamRule
      · exact church_pair_ab_type
      · exact HasType.appRule
          [shift 0 1 churchPairABTy, Term.sort, Term.sort]
          (Term.app (Term.var 0) (Term.var 1))
          (Term.lam (Term.var 2) (Term.lam (Term.var 2) (Term.var 0)))
          (Term.pi (Term.var 2) (Term.pi (Term.var 2) (Term.var 3)))
          (Term.var 2)
          (HasType.appRule
            [shift 0 1 churchPairABTy, Term.sort, Term.sort]
            (Term.var 0)
            (Term.var 1)
            Term.sort
            (Term.pi
              (Term.pi (Term.var 3)
                (Term.pi (Term.var 3) (Term.var 2)))
              (Term.var 1))
            (HasType.varRule
              [shift 0 1 churchPairABTy, Term.sort, Term.sort]
              0
              (Term.pi Term.sort
                (Term.pi
                  (Term.pi (Term.var 3)
                    (Term.pi (Term.var 3) (Term.var 2)))
                  (Term.var 1)))
              rfl)
            (HasType.varRule
              [shift 0 1 churchPairABTy, Term.sort, Term.sort]
              1
              Term.sort
              rfl))
          (HasType.lamRule
            [shift 0 1 churchPairABTy, Term.sort, Term.sort]
            (Term.var 2)
            (Term.lam (Term.var 2) (Term.var 0))
            (Term.pi (Term.var 2) (Term.var 3))
            (HasType.varRule
              [shift 0 1 churchPairABTy, Term.sort, Term.sort]
              2
              Term.sort
              rfl)
            (HasType.lamRule
              [Term.var 3, shift 0 1 churchPairABTy, Term.sort, Term.sort]
              (Term.var 2)
              (Term.var 0)
              (Term.var 3)
              (HasType.varRule
                [Term.var 3, shift 0 1 churchPairABTy, Term.sort, Term.sort]
                2
                Term.sort
                rfl)
              (HasType.varRule
                [Term.var 3, Term.var 3, shift 0 1 churchPairABTy, Term.sort, Term.sort]
                0
                (Term.var 3)
                rfl)))

theorem church_pair_former :
    HasType [] churchPairFormerTm churchPairFormerTy := by
  apply HasType.lamRule
  · exact HasType.sortRule []
  · apply HasType.lamRule
    · exact HasType.sortRule [Term.sort]
    · exact church_pair_ab_type

theorem church_pair_bool_nat_type :
    HasType []
      (Term.app
        (Term.app churchPairFormerTm churchBoolTy)
        churchNatTy)
      Term.sort := by
  exact HasType.appRule []
    (Term.app churchPairFormerTm churchBoolTy)
    churchNatTy
    Term.sort
    Term.sort
    (HasType.appRule []
      churchPairFormerTm
      churchBoolTy
      Term.sort
      (Term.pi Term.sort Term.sort)
      church_pair_former
      church_bool_type)
    church_nat_type

abbrev churchOptionATy : Term :=
  Term.pi Term.sort
    (Term.pi (Term.var 0)
      (Term.pi
        (Term.pi (Term.var 2) (Term.var 2))
        (Term.var 2)))

abbrev churchOptionTy : Term :=
  Term.pi Term.sort churchOptionATy

abbrev churchNoneTy : Term :=
  churchOptionTy

abbrev churchNoneTm : Term :=
  Term.lam Term.sort
    (Term.lam Term.sort
      (Term.lam (Term.var 0)
        (Term.lam
          (Term.pi (Term.var 2) (Term.var 2))
          (Term.var 1))))

abbrev churchSomeTy : Term :=
  Term.pi Term.sort
    (Term.pi (Term.var 0)
      (Term.pi Term.sort
        (Term.pi (Term.var 0)
          (Term.pi
            (Term.pi (Term.var 3) (Term.var 2))
            (Term.var 2)))))

abbrev churchSomeTm : Term :=
  Term.lam Term.sort
    (Term.lam (Term.var 0)
      (Term.lam Term.sort
        (Term.lam (Term.var 0)
          (Term.lam
            (Term.pi (Term.var 3) (Term.var 2))
            (Term.app (Term.var 0) (Term.var 3))))))

abbrev churchOptionAInCaseCtxTy : Term :=
  Term.pi Term.sort
    (Term.pi (Term.var 0)
      (Term.pi
        (Term.pi (Term.var 3) (Term.var 2))
        (Term.var 2)))

abbrev churchCaseOptionTy : Term :=
  Term.pi Term.sort
    (Term.pi Term.sort
      (Term.pi churchOptionAInCaseCtxTy
        (Term.pi (Term.var 1)
          (Term.pi
            (Term.pi (Term.var 3) (Term.var 3))
            (Term.var 3)))))

abbrev churchCaseOptionTm : Term :=
  Term.lam Term.sort
    (Term.lam Term.sort
      (Term.lam churchOptionAInCaseCtxTy
        (Term.lam (Term.var 1)
          (Term.lam
            (Term.pi (Term.var 3) (Term.var 3))
            (Term.app
              (Term.app
                (Term.app (Term.var 2) (Term.var 3))
                (Term.var 1))
              (Term.var 0))))))

theorem church_option_at_type :
    HasType [Term.sort] churchOptionATy Term.sort := by
  apply HasType.piRule
  · exact HasType.sortRule [Term.sort]
  · apply HasType.piRule
    · apply HasType.varRule
      rfl
    · apply HasType.piRule
      · apply HasType.piRule
        · apply HasType.varRule
          rfl
        · apply HasType.varRule
          rfl
      · apply HasType.varRule
        rfl

theorem church_option_type :
    HasType [] churchOptionTy Term.sort := by
  apply HasType.piRule
  · exact HasType.sortRule []
  · exact church_option_at_type

theorem church_none_type :
    HasType [] churchNoneTy Term.sort := by
  exact church_option_type

theorem church_none :
    HasType [] churchNoneTm churchNoneTy := by
  apply HasType.lamRule
  · exact HasType.sortRule []
  · apply HasType.lamRule
    · exact HasType.sortRule [Term.sort]
    · apply HasType.lamRule
      · apply HasType.varRule
        rfl
      · apply HasType.lamRule
        · apply HasType.piRule
          · apply HasType.varRule
            rfl
          · apply HasType.varRule
            rfl
        · apply HasType.varRule
          rfl

theorem church_some_type :
    HasType [] churchSomeTy Term.sort := by
  apply HasType.piRule
  · exact HasType.sortRule []
  · apply HasType.piRule
    · apply HasType.varRule
      rfl
    · apply HasType.piRule
      · exact HasType.sortRule [Term.var 1, Term.sort]
      · apply HasType.piRule
        · apply HasType.varRule
          rfl
        · apply HasType.piRule
          · apply HasType.piRule
            · apply HasType.varRule
              rfl
            · apply HasType.varRule
              rfl
          · apply HasType.varRule
            rfl

theorem church_some :
    HasType [] churchSomeTm churchSomeTy := by
  apply HasType.lamRule
  · exact HasType.sortRule []
  · apply HasType.lamRule
    · apply HasType.varRule
      rfl
    · apply HasType.lamRule
      · exact HasType.sortRule [Term.var 1, Term.sort]
      · apply HasType.lamRule
        · apply HasType.varRule
          rfl
        · apply HasType.lamRule
          · apply HasType.piRule
            · apply HasType.varRule
              rfl
            · apply HasType.varRule
              rfl
          · exact HasType.appRule
              [Term.pi (Term.var 4) (Term.var 3),
                Term.var 1,
                Term.sort,
                Term.var 1,
                Term.sort]
              (Term.var 0)
              (Term.var 3)
              (Term.var 4)
              (Term.var 3)
              (HasType.varRule
                [Term.pi (Term.var 4) (Term.var 3),
                  Term.var 1,
                  Term.sort,
                  Term.var 1,
                  Term.sort]
                0
                (Term.pi (Term.var 4) (Term.var 3))
                rfl)
              (HasType.varRule
                [Term.pi (Term.var 4) (Term.var 3),
                  Term.var 1,
                  Term.sort,
                  Term.var 1,
                  Term.sort]
                3
                (Term.var 4)
                rfl)

theorem church_option_in_case_ctx_type :
    HasType [Term.sort, Term.sort] churchOptionAInCaseCtxTy Term.sort := by
  apply HasType.piRule
  · exact HasType.sortRule [Term.sort, Term.sort]
  · apply HasType.piRule
    · apply HasType.varRule
      rfl
    · apply HasType.piRule
      · apply HasType.piRule
        · apply HasType.varRule
          rfl
        · apply HasType.varRule
          rfl
      · apply HasType.varRule
        rfl

theorem church_case_option_type :
    HasType [] churchCaseOptionTy Term.sort := by
  apply HasType.piRule
  · exact HasType.sortRule []
  · apply HasType.piRule
    · exact HasType.sortRule [Term.sort]
    · apply HasType.piRule
      · exact church_option_in_case_ctx_type
      · apply HasType.piRule
        · apply HasType.varRule
          rfl
        · apply HasType.piRule
          · apply HasType.piRule
            · apply HasType.varRule
              rfl
            · apply HasType.varRule
              rfl
          · apply HasType.varRule
            rfl

theorem church_case_option :
    HasType [] churchCaseOptionTm churchCaseOptionTy := by
  apply HasType.lamRule
  · exact HasType.sortRule []
  · apply HasType.lamRule
    · exact HasType.sortRule [Term.sort]
    · apply HasType.lamRule
      · exact church_option_in_case_ctx_type
      · apply HasType.lamRule
        · apply HasType.varRule
          rfl
        · apply HasType.lamRule
          · apply HasType.piRule
            · apply HasType.varRule
              rfl
            · apply HasType.varRule
              rfl
          · exact HasType.appRule
              [Term.pi (Term.var 4) (Term.var 4),
                Term.var 2,
                shift 0 1 churchOptionAInCaseCtxTy,
                Term.sort,
                Term.sort]
              (Term.app
                (Term.app (Term.var 2) (Term.var 3))
                (Term.var 1))
              (Term.var 0)
              (Term.pi (Term.var 4) (Term.var 4))
              (Term.var 4)
              (HasType.appRule
                [Term.pi (Term.var 4) (Term.var 4),
                  Term.var 2,
                  shift 0 1 churchOptionAInCaseCtxTy,
                  Term.sort,
                  Term.sort]
                (Term.app (Term.var 2) (Term.var 3))
                (Term.var 1)
                (Term.var 3)
                (Term.pi
                  (Term.pi (Term.var 5) (Term.var 5))
                  (Term.var 5))
                (HasType.appRule
                  [Term.pi (Term.var 4) (Term.var 4),
                    Term.var 2,
                    shift 0 1 churchOptionAInCaseCtxTy,
                    Term.sort,
                    Term.sort]
                  (Term.var 2)
                  (Term.var 3)
                  Term.sort
                  (Term.pi (Term.var 0)
                    (Term.pi
                      (Term.pi (Term.var 6) (Term.var 2))
                      (Term.var 2)))
                  (HasType.varRule
                    [Term.pi (Term.var 4) (Term.var 4),
                      Term.var 2,
                      shift 0 1 churchOptionAInCaseCtxTy,
                      Term.sort,
                      Term.sort]
                    2
                    (Term.pi Term.sort
                      (Term.pi (Term.var 0)
                        (Term.pi
                          (Term.pi (Term.var 6) (Term.var 2))
                          (Term.var 2))))
                    rfl)
                  (HasType.varRule
                    [Term.pi (Term.var 4) (Term.var 4),
                      Term.var 2,
                      shift 0 1 churchOptionAInCaseCtxTy,
                      Term.sort,
                      Term.sort]
                    3
                    Term.sort
                    rfl))
                (HasType.varRule
                  [Term.pi (Term.var 4) (Term.var 4),
                    Term.var 2,
                    shift 0 1 churchOptionAInCaseCtxTy,
                    Term.sort,
                    Term.sort]
                  1
                  (Term.var 3)
                  rfl))
              (HasType.varRule
                [Term.pi (Term.var 4) (Term.var 4),
                  Term.var 2,
                  shift 0 1 churchOptionAInCaseCtxTy,
                  Term.sort,
                  Term.sort]
                0
                (Term.pi (Term.var 4) (Term.var 4))
                rfl)

end BEDC.MetaCIC
