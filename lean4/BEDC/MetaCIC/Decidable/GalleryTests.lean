import BEDC.MetaCIC.Decidable.CheckClosed
import BEDC.MetaCIC.Decidable.CheckCompleteness
import BEDC.MetaCIC.TypedExamples.ChurchGallery
import BEDC.MetaCIC.TypedExamples.ChurchNatRec
import BEDC.MetaCIC.TypedExamples.ChurchNatArith
import BEDC.MetaCIC.TypedExamples.ChurchSum
import BEDC.MetaCIC.TypedExamples.ChurchList
import BEDC.MetaCIC.TypedExamples.Polymorphic

namespace BEDC.MetaCIC

abbrev polyIdentityTm : Term :=
  Term.lam Term.sort (Term.lam (Term.var 0) (Term.var 0))

abbrev polyIdentityTy : Term :=
  Term.pi Term.sort (Term.pi (Term.var 0) (Term.var 1))

abbrev polyConstTm : Term :=
  Term.lam Term.sort
    (Term.lam Term.sort
      (Term.lam (Term.var 1)
        (Term.lam (Term.var 1) (Term.var 1))))

abbrev polyConstTy : Term :=
  Term.pi Term.sort
    (Term.pi Term.sort
      (Term.pi (Term.var 1)
        (Term.pi (Term.var 1) (Term.var 3))))

abbrev polyApplyTm : Term :=
  Term.lam Term.sort
    (Term.lam Term.sort
      (Term.lam (Term.pi (Term.var 1) (Term.var 1))
        (Term.lam (Term.var 2)
          (Term.app (Term.var 1) (Term.var 0)))))

abbrev polyApplyTy : Term :=
  Term.pi Term.sort
    (Term.pi Term.sort
      (Term.pi (Term.pi (Term.var 1) (Term.var 1))
        (Term.pi (Term.var 2) (Term.var 2))))

abbrev polyFlipTm : Term :=
  Term.lam Term.sort
    (Term.lam Term.sort
      (Term.lam Term.sort
        (Term.lam
          (Term.pi (Term.var 2)
            (Term.pi (Term.var 2) (Term.var 2)))
          (Term.lam (Term.var 2)
            (Term.lam (Term.var 4)
              (Term.app
                (Term.app (Term.var 2) (Term.var 0))
                (Term.var 1)))))))

abbrev polyFlipTy : Term :=
  Term.pi Term.sort
    (Term.pi Term.sort
      (Term.pi Term.sort
        (Term.pi
          (Term.pi (Term.var 2)
            (Term.pi (Term.var 2) (Term.var 2)))
          (Term.pi (Term.var 2)
            (Term.pi (Term.var 4) (Term.var 3))))))

abbrev polyComposeTm : Term :=
  Term.lam Term.sort
    (Term.lam Term.sort
      (Term.lam Term.sort
        (Term.lam (Term.pi (Term.var 1) (Term.var 1))
          (Term.lam (Term.pi (Term.var 3) (Term.var 3))
            (Term.lam (Term.var 4)
              (Term.app (Term.var 2)
                (Term.app (Term.var 1) (Term.var 0))))))))

abbrev polyComposeTy : Term :=
  Term.pi Term.sort
    (Term.pi Term.sort
      (Term.pi Term.sort
        (Term.pi (Term.pi (Term.var 1) (Term.var 1))
          (Term.pi (Term.pi (Term.var 3) (Term.var 3))
            (Term.pi (Term.var 4) (Term.var 3))))))

abbrev polyIdentityAtSortTm : Term :=
  Term.app polyIdentityTm Term.sort

abbrev polyIdentityAtSortTy : Term :=
  Term.pi Term.sort Term.sort

example : inferTypeCtx [] churchBoolTy = some Term.sort := by
  rfl

example : inferTypeCtx [] churchTrueTm = some churchBoolTy := by
  rfl

example : inferTypeCtx [] churchFalseTm = some churchBoolTy := by
  rfl

example : inferTypeCtx [] churchNatTy = some Term.sort := by
  rfl

example : inferTypeCtx [] churchZeroTm = some churchNatTy := by
  rfl

example : inferTypeCtx [] churchOneTm = some churchNatTy := by
  rfl

example : inferTypeCtx [] churchSuccTy = some Term.sort := by
  rfl

example : inferTypeCtx [] churchSuccTm = some churchSuccTy := by
  rfl

example :
    inferTypeCtx [] ChurchNatRec.church_succ = some churchSuccTy := by
  rfl

example :
    inferTypeCtx [] ChurchNatRec.church_add =
      some ChurchNatRec.church_add_type_tm := by
  rfl

example : inferTypeCtx [] church_mul = some church_nat_binop_type_tm := by
  rfl

example : inferTypeCtx [] church_exp = some church_nat_binop_type_tm := by
  rfl

example : inferTypeCtx [] churchPairTy = some Term.sort := by
  rfl

example : inferTypeCtx [] churchPairFormerTm = some churchPairFormerTy := by
  rfl

example : inferTypeCtx [] churchMkPairTy = some Term.sort := by
  rfl

example : inferTypeCtx [] churchMkPairTm = some churchMkPairTy := by
  rfl

example : inferTypeCtx [] churchFstTy = some Term.sort := by
  rfl

example : inferTypeCtx [] churchFstTm = some churchFstTy := by
  rfl

example : inferTypeCtx [] churchSndTy = some Term.sort := by
  rfl

example : inferTypeCtx [] churchSndTm = some churchSndTy := by
  rfl

example : inferTypeCtx [] churchOptionTy = some Term.sort := by
  rfl

example : inferTypeCtx [] churchNoneTy = some Term.sort := by
  rfl

example : inferTypeCtx [] churchNoneTm = some churchNoneTy := by
  rfl

example : inferTypeCtx [] churchSomeTy = some Term.sort := by
  rfl

example : inferTypeCtx [] churchSomeTm = some churchSomeTy := by
  rfl

example : inferTypeCtx [] churchCaseOptionTy = some Term.sort := by
  rfl

example : inferTypeCtx [] churchCaseOptionTm = some churchCaseOptionTy := by
  rfl

example : inferTypeCtx [] church_list_type = some church_list_type_ty := by
  rfl

example : inferTypeCtx [] church_nil = some church_nil_type := by
  rfl

example : inferTypeCtx [] church_cons_type = some Term.sort := by
  rfl

example : inferTypeCtx [] church_cons = some church_cons_type := by
  rfl

example : inferTypeCtx [] church_fold_type = some Term.sort := by
  rfl

example : inferTypeCtx [] church_fold = some church_fold_type := by
  rfl

example : inferTypeCtx [] church_either_type = some Term.sort := by
  rfl

example : inferTypeCtx [] church_inl = some church_inl_type := by
  rfl

example : inferTypeCtx [] church_inr = some church_inr_type := by
  rfl

example : inferTypeCtx [] church_case_either = some church_case_either_type := by
  rfl

example : inferTypeCtx [] polyIdentityTm = some polyIdentityTy := by
  rfl

example : inferTypeCtx [] polyConstTm = some polyConstTy := by
  rfl

example : inferTypeCtx [] polyApplyTm = some polyApplyTy := by
  rfl

example : inferTypeCtx [] polyFlipTm = some polyFlipTy := by
  rfl

example : inferTypeCtx [] polyComposeTm = some polyComposeTy := by
  rfl

example : inferTypeCtx [] polyIdentityAtSortTm = some polyIdentityAtSortTy := by
  rfl

example : inferTypeCtx [] (Term.var 0) = none := by
  rfl

theorem gallery_sanity_bool_witnesses :
    inferTypeCtx [] churchTrueTm ≠ none
    ∧ inferTypeCtx [] churchFalseTm ≠ none := by
  constructor
  · intro h
    cases h
  · intro h
    cases h

theorem gallery_sanity_nat_witnesses :
    inferTypeCtx [] churchZeroTm ≠ none
    ∧ inferTypeCtx [] churchOneTm ≠ none
    ∧ inferTypeCtx [] churchSuccTm ≠ none
    ∧ inferTypeCtx [] ChurchNatRec.church_add ≠ none
    ∧ inferTypeCtx [] church_mul ≠ none
    ∧ inferTypeCtx [] church_exp ≠ none := by
  constructor
  · intro h
    cases h
  constructor
  · intro h
    cases h
  constructor
  · intro h
    cases h
  constructor
  · intro h
    cases h
  constructor
  · intro h
    cases h
  · intro h
    cases h

theorem gallery_sanity_pair_witnesses :
    inferTypeCtx [] churchPairFormerTm ≠ none
    ∧ inferTypeCtx [] churchMkPairTm ≠ none
    ∧ inferTypeCtx [] churchFstTm ≠ none
    ∧ inferTypeCtx [] churchSndTm ≠ none := by
  constructor
  · intro h
    cases h
  constructor
  · intro h
    cases h
  constructor
  · intro h
    cases h
  · intro h
    cases h

theorem gallery_sanity_option_witnesses :
    inferTypeCtx [] churchNoneTm ≠ none
    ∧ inferTypeCtx [] churchSomeTm ≠ none
    ∧ inferTypeCtx [] churchCaseOptionTm ≠ none := by
  constructor
  · intro h
    cases h
  constructor
  · intro h
    cases h
  · intro h
    cases h

theorem gallery_sanity_list_witnesses :
    inferTypeCtx [] church_list_type ≠ none
    ∧ inferTypeCtx [] church_nil ≠ none
    ∧ inferTypeCtx [] church_cons ≠ none
    ∧ inferTypeCtx [] church_fold ≠ none := by
  constructor
  · intro h
    cases h
  constructor
  · intro h
    cases h
  constructor
  · intro h
    cases h
  · intro h
    cases h

theorem gallery_sanity_sum_witnesses :
    inferTypeCtx [] church_inl ≠ none
    ∧ inferTypeCtx [] church_inr ≠ none
    ∧ inferTypeCtx [] church_case_either ≠ none := by
  constructor
  · intro h
    cases h
  constructor
  · intro h
    cases h
  · intro h
    cases h

theorem gallery_sanity_polymorphic_witnesses :
    inferTypeCtx [] polyIdentityTm ≠ none
    ∧ inferTypeCtx [] polyConstTm ≠ none
    ∧ inferTypeCtx [] polyApplyTm ≠ none
    ∧ inferTypeCtx [] polyFlipTm ≠ none
    ∧ inferTypeCtx [] polyComposeTm ≠ none
    ∧ inferTypeCtx [] polyIdentityAtSortTm ≠ none := by
  constructor
  · intro h
    cases h
  constructor
  · intro h
    cases h
  constructor
  · intro h
    cases h
  constructor
  · intro h
    cases h
  constructor
  · intro h
    cases h
  · intro h
    cases h

theorem gallery_sanity_all_typed_witnesses :
    inferTypeCtx [] churchTrueTm ≠ none
    ∧ inferTypeCtx [] churchFalseTm ≠ none
    ∧ inferTypeCtx [] churchZeroTm ≠ none
    ∧ inferTypeCtx [] churchOneTm ≠ none
    ∧ inferTypeCtx [] churchSuccTm ≠ none
    ∧ inferTypeCtx [] ChurchNatRec.church_add ≠ none
    ∧ inferTypeCtx [] church_mul ≠ none
    ∧ inferTypeCtx [] church_exp ≠ none
    ∧ inferTypeCtx [] churchPairFormerTm ≠ none
    ∧ inferTypeCtx [] churchMkPairTm ≠ none
    ∧ inferTypeCtx [] churchFstTm ≠ none
    ∧ inferTypeCtx [] churchSndTm ≠ none
    ∧ inferTypeCtx [] churchNoneTm ≠ none
    ∧ inferTypeCtx [] churchSomeTm ≠ none
    ∧ inferTypeCtx [] churchCaseOptionTm ≠ none
    ∧ inferTypeCtx [] church_nil ≠ none
    ∧ inferTypeCtx [] church_cons ≠ none
    ∧ inferTypeCtx [] church_inl ≠ none
    ∧ inferTypeCtx [] church_inr ≠ none
    ∧ inferTypeCtx [] polyIdentityTm ≠ none
    ∧ inferTypeCtx [] polyConstTm ≠ none := by
  constructor
  · intro h
    cases h
  constructor
  · intro h
    cases h
  constructor
  · intro h
    cases h
  constructor
  · intro h
    cases h
  constructor
  · intro h
    cases h
  constructor
  · intro h
    cases h
  constructor
  · intro h
    cases h
  constructor
  · intro h
    cases h
  constructor
  · intro h
    cases h
  constructor
  · intro h
    cases h
  constructor
  · intro h
    cases h
  constructor
  · intro h
    cases h
  constructor
  · intro h
    cases h
  constructor
  · intro h
    cases h
  constructor
  · intro h
    cases h
  constructor
  · intro h
    cases h
  constructor
  · intro h
    cases h
  constructor
  · intro h
    cases h
  constructor
  · intro h
    cases h
  constructor
  · intro h
    cases h
  · intro h
    cases h

end BEDC.MetaCIC
