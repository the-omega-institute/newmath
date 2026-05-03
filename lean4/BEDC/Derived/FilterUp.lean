import BEDC.FKernel.Unary

namespace BEDC.Derived.FilterUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Cont
open BEDC.FKernel.Unary

theorem FilterPrincipalSuffix_unary_intersection_closed
    {base left right meet leftPoint rightPoint meetPoint : BHist} :
    UnaryHistory base -> UnaryHistory left -> UnaryHistory right -> Cont left right meet ->
      Cont base left leftPoint -> Cont base right rightPoint -> Cont base meet meetPoint ->
        UnaryHistory meetPoint ∧ Cont leftPoint right meetPoint ∧
          Cont rightPoint left meetPoint := by
  intro baseCarrier leftCarrier rightCarrier leftRight baseLeft baseRight baseMeet
  have meetCarrier : UnaryHistory meet :=
    unary_cont_closed leftCarrier rightCarrier leftRight
  have meetPointCarrier : UnaryHistory meetPoint :=
    unary_cont_closed baseCarrier meetCarrier baseMeet
  have leftProjection : Cont leftPoint right meetPoint := by
    cases baseMeet
    cases baseLeft
    cases leftRight
    exact cont_intro (append_assoc base left right).symm
  have rightProjection : Cont rightPoint left meetPoint := by
    cases baseMeet
    cases baseRight
    cases leftRight
    exact cont_intro
      ((congrArg (fun tail => append base tail)
        (unary_append_comm leftCarrier rightCarrier)).trans
          (append_assoc base right left).symm)
  exact And.intro meetPointCarrier (And.intro leftProjection rightProjection)

theorem FilterPrincipalSuffix_unary_intersection_result_deterministic
    {base left right meet leftPoint rightPoint meetPoint displayed : BHist} :
    UnaryHistory base -> UnaryHistory left -> UnaryHistory right -> Cont left right meet ->
      Cont base left leftPoint -> Cont base right rightPoint -> Cont base meet meetPoint ->
        Cont rightPoint left displayed -> hsame meetPoint displayed := by
  intro baseCarrier leftCarrier rightCarrier leftRight baseLeft baseRight baseMeet displayedRel
  have closed :=
    FilterPrincipalSuffix_unary_intersection_closed
      baseCarrier leftCarrier rightCarrier leftRight baseLeft baseRight baseMeet
  exact cont_deterministic closed.right.right displayedRel

end BEDC.Derived.FilterUp
