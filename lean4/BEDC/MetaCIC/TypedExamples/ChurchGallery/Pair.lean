import BEDC.MetaCIC.TypedExamples.ChurchGallery.BoolNat

namespace BEDC.MetaCIC

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

end BEDC.MetaCIC
