import BEDC.MetaCIC.BHistSubstrate
import BEDC.MetaCIC.Decidable.GalleryTests

namespace BEDC.MetaCIC

theorem gallery_obligation_matrix :
    (HasType [] churchTrueTm churchBoolTy ∧ inferTypeCtx [] churchTrueTm = some churchBoolTy) ∧
      (HasType [] churchZeroTm churchNatTy ∧
        inferTypeCtx [] churchZeroTm = some churchNatTy) ∧
        (HasType [] church_nil church_nil_type ∧
          inferTypeCtx [] church_nil = some church_nil_type) ∧
          (HasType [] church_inl church_inl_type ∧
            inferTypeCtx [] church_inl = some church_inl_type) ∧
            BEDC.MetaCIC.BHistSubstrate.bhistToTerm BEDC.FKernel.Hist.BHist.Empty =
              BEDC.MetaCIC.Term.lam BEDC.MetaCIC.Term.sort
                (BEDC.MetaCIC.Term.lam BEDC.MetaCIC.Term.sort
                  (BEDC.MetaCIC.Term.lam BEDC.MetaCIC.Term.sort
                    (BEDC.MetaCIC.Term.var 2))) := by
  -- BEDC touchpoint anchor: BEDC.MetaCIC.Term BEDC.FKernel.Hist.BHist BHist
  have boolTyped : HasType [] churchTrueTm churchBoolTy := church_true
  have natTyped : HasType [] churchZeroTm churchNatTy := church_zero
  have nilTyped : HasType [] church_nil church_nil_type := church_nil_typed
  have inlTyped : HasType [] church_inl church_inl_type := church_inl_typed
  have boolChecked :
      inferTypeCtx [] churchTrueTm = some churchBoolTy :=
    CheckCompleteness.inferTypeCtx_complete_raw [] churchTrueTm churchBoolTy boolTyped
  have natChecked :
      inferTypeCtx [] churchZeroTm = some churchNatTy :=
    CheckCompleteness.inferTypeCtx_complete_raw [] churchZeroTm churchNatTy natTyped
  have nilChecked :
      inferTypeCtx [] church_nil = some church_nil_type :=
    CheckCompleteness.inferTypeCtx_complete_raw [] church_nil church_nil_type nilTyped
  have inlChecked :
      inferTypeCtx [] church_inl = some church_inl_type :=
    CheckCompleteness.inferTypeCtx_complete_raw [] church_inl church_inl_type inlTyped
  exact
    ⟨⟨boolTyped, boolChecked⟩,
      ⟨⟨natTyped, natChecked⟩,
        ⟨⟨nilTyped, nilChecked⟩, ⟨⟨inlTyped, inlChecked⟩, rfl⟩⟩⟩⟩

end BEDC.MetaCIC
