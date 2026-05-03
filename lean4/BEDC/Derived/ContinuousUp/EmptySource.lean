import BEDC.Derived.ContinuousUp

namespace BEDC.Derived.ContinuousUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Cont
open BEDC.FKernel.Unary

theorem ContinuousModulusWitness_empty_source_iff {modulus target : BHist} :
    ContinuousModulusWitness BHist.Empty modulus target ↔
      UnaryHistory target ∧ hsame modulus target := by
  constructor
  · intro witness
    cases witness with
    | intro _sourceCarrier rest =>
        cases rest with
        | intro _modulusCarrier rest =>
            cases rest with
            | intro targetCarrier modulusRel =>
                exact
                  And.intro targetCarrier
                    (hsame_symm (cont_left_unit_result modulusRel))
  · intro data
    cases data with
    | intro targetCarrier sameModulus =>
        exact
          And.intro unary_empty
            (And.intro
              (unary_transport targetCarrier (hsame_symm sameModulus))
              (And.intro targetCarrier
                (Iff.mpr cont_left_unit_iff (hsame_symm sameModulus))))

theorem ContinuousModulusWitness_empty_source_nonempty_modulus_shape_iff
    {target modulus : BHist} :
    (ContinuousModulusWitness BHist.Empty modulus target /\
      (hsame modulus BHist.Empty -> False)) <->
      exists r : BHist, target = BHist.e1 r /\ modulus = BHist.e1 r /\ UnaryHistory r := by
  constructor
  · intro data
    have sourceData :=
      (ContinuousModulusWitness_empty_source_iff (modulus := modulus)
        (target := target)).mp data.left
    cases target with
    | Empty =>
        exact False.elim (data.right sourceData.right)
    | e0 t =>
        exact False.elim (unary_no_zero_extension sourceData.left)
    | e1 r =>
        cases sourceData.right
        exact Exists.intro r
          (And.intro rfl (And.intro rfl (unary_e1_inversion sourceData.left)))
  · intro witness
    cases witness with
    | intro r data =>
        cases data with
        | intro targetEq rest =>
            cases rest with
            | intro modulusEq tailCarrier =>
                cases targetEq
                cases modulusEq
                constructor
                · exact (ContinuousModulusWitness_empty_source_iff
                    (modulus := BHist.e1 r) (target := BHist.e1 r)).mpr
                    (And.intro (unary_e1_closed tailCarrier) (hsame_refl (BHist.e1 r)))
                · intro sameEmpty
                  exact not_hsame_e1_empty sameEmpty

end BEDC.Derived.ContinuousUp
