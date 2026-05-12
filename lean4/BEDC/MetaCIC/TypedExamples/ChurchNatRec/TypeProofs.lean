import BEDC.MetaCIC.TypedExamples.ChurchNatRec.Reductions

namespace BEDC.MetaCIC
namespace ChurchNatRec

theorem church_succ_type :
    HasType [] church_succ churchSuccTy := by
  exact BEDC.MetaCIC.church_succ

theorem church_succ_type_in_ctx :
    HasType [churchNatTy] churchSuccTm churchSuccTy := by
  unfold churchSuccTm
  apply HasType.lamRule
  · exact church_nat_type_in_ctx
  · apply HasType.lamRule
    · exact HasType.sortRule [churchNatTy, churchNatTy]
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
              churchNatTy,
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
                churchNatTy,
                churchNatTy]
              1
              (Term.pi (Term.var 2) (Term.var 3))
              rfl)
            (HasType.appRule
              [Term.var 2,
                Term.pi (Term.var 1) (Term.var 2),
                Term.sort,
                churchNatTy,
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
                  churchNatTy,
                  churchNatTy]
                (Term.app (Term.var 3) (Term.var 2))
                (Term.var 1)
                (Term.pi (Term.var 2) (Term.var 3))
                (Term.pi (Term.var 3) (Term.var 4))
                (HasType.appRule
                  [Term.var 2,
                    Term.pi (Term.var 1) (Term.var 2),
                    Term.sort,
                    churchNatTy,
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
                      churchNatTy,
                      churchNatTy]
                    3
                    churchNatTy
                    rfl)
                  (HasType.varRule
                    [Term.var 2,
                      Term.pi (Term.var 1) (Term.var 2),
                      Term.sort,
                      churchNatTy,
                      churchNatTy]
                    2
                    Term.sort
                    rfl))
                (HasType.varRule
                  [Term.var 2,
                    Term.pi (Term.var 1) (Term.var 2),
                    Term.sort,
                    churchNatTy,
                    churchNatTy]
                  1
                  (Term.pi (Term.var 2) (Term.var 3))
                  rfl))
              (HasType.varRule
                [Term.var 2,
                  Term.pi (Term.var 1) (Term.var 2),
                  Term.sort,
                  churchNatTy,
                  churchNatTy]
                0
                (Term.var 2)
                rfl))

theorem church_succ_type_in_two_ctx :
    HasType [churchNatTy, churchNatTy] churchSuccTm churchSuccTy := by
  unfold churchSuccTm
  apply HasType.lamRule
  · exact church_nat_type_in_two_ctx
  · apply HasType.lamRule
    · exact HasType.sortRule [churchNatTy, churchNatTy, churchNatTy]
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
              churchNatTy,
              churchNatTy,
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
                churchNatTy,
                churchNatTy,
                churchNatTy]
              1
              (Term.pi (Term.var 2) (Term.var 3))
              rfl)
            (HasType.appRule
              [Term.var 2,
                Term.pi (Term.var 1) (Term.var 2),
                Term.sort,
                churchNatTy,
                churchNatTy,
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
                  churchNatTy,
                  churchNatTy,
                  churchNatTy]
                (Term.app (Term.var 3) (Term.var 2))
                (Term.var 1)
                (Term.pi (Term.var 2) (Term.var 3))
                (Term.pi (Term.var 3) (Term.var 4))
                (HasType.appRule
                  [Term.var 2,
                    Term.pi (Term.var 1) (Term.var 2),
                    Term.sort,
                    churchNatTy,
                    churchNatTy,
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
                      churchNatTy,
                      churchNatTy,
                      churchNatTy]
                    3
                    churchNatTy
                    rfl)
                  (HasType.varRule
                    [Term.var 2,
                      Term.pi (Term.var 1) (Term.var 2),
                      Term.sort,
                      churchNatTy,
                      churchNatTy,
                      churchNatTy]
                    2
                    Term.sort
                    rfl))
                (HasType.varRule
                  [Term.var 2,
                    Term.pi (Term.var 1) (Term.var 2),
                    Term.sort,
                    churchNatTy,
                    churchNatTy,
                    churchNatTy]
                  1
                  (Term.pi (Term.var 2) (Term.var 3))
                  rfl))
              (HasType.varRule
                [Term.var 2,
                  Term.pi (Term.var 1) (Term.var 2),
                  Term.sort,
                  churchNatTy,
                  churchNatTy,
                  churchNatTy]
                0
                (Term.var 2)
                rfl))

theorem church_add_body_type :
    HasType [churchNatTy, churchNatTy]
      (Term.app
        (Term.app
          (Term.app (Term.var 1) churchNatTy)
          churchSuccTm)
        (Term.var 0))
      churchNatTy := by
  exact HasType.appRule
    [churchNatTy, churchNatTy]
    (Term.app
      (Term.app (Term.var 1) churchNatTy)
      churchSuccTm)
    (Term.var 0)
    churchNatTy
    churchNatTy
    (HasType.appRule
      [churchNatTy, churchNatTy]
      (Term.app (Term.var 1) churchNatTy)
      churchSuccTm
      churchSuccTy
      churchSuccTy
      (HasType.appRule
        [churchNatTy, churchNatTy]
        (Term.var 1)
        churchNatTy
        Term.sort
        (Term.pi
          (Term.pi (Term.var 0) (Term.var 1))
          (Term.pi (Term.var 1) (Term.var 2)))
        (HasType.varRule
          [churchNatTy, churchNatTy]
          1
          churchNatTy
          rfl)
        church_nat_type_in_two_ctx)
      church_succ_type_in_two_ctx)
    (HasType.varRule
      [churchNatTy, churchNatTy]
      0
      churchNatTy
      rfl)

theorem church_add_type :
    HasType [] church_add church_add_type_tm := by
  unfold church_add
  unfold church_add_type_tm
  apply HasType.lamRule
  · exact church_nat_type
  · apply HasType.lamRule
    · exact church_nat_type_in_ctx
    · exact church_add_body_type
end ChurchNatRec
end BEDC.MetaCIC
