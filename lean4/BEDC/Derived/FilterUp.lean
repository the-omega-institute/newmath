import BEDC.FKernel.NameCert
import BEDC.FKernel.Unary

namespace BEDC.Derived.FilterUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Cont
open BEDC.FKernel.NameCert
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

theorem FilterPrincipalSuffix_unary_commuting_square
    {base left right leftPoint rightPoint lrPoint rlPoint : BHist} :
    UnaryHistory left -> UnaryHistory right -> Cont base left leftPoint ->
      Cont base right rightPoint -> Cont leftPoint right lrPoint ->
        Cont rightPoint left rlPoint -> hsame lrPoint rlPoint := by
  intro leftCarrier rightCarrier baseLeft baseRight leftThenRight rightThenLeft
  cases baseLeft
  cases baseRight
  cases leftThenRight
  cases rightThenLeft
  exact hsame_trans (append_assoc base left right)
    (hsame_trans
      (congrArg (fun tail => append base tail)
        (unary_append_comm leftCarrier rightCarrier))
      (hsame_symm (append_assoc base right left)))

theorem FilterPrincipalSuffix_unary_intersection_commuted_meet_closed
    {base left right meet meetPoint : BHist} :
    UnaryHistory left -> UnaryHistory right -> Cont left right meet -> Cont base meet meetPoint ->
      Cont base (append right left) meetPoint := by
  intro leftCarrier rightCarrier leftRight baseMeet
  cases baseMeet
  cases leftRight
  exact cont_intro (congrArg (fun tail => append base tail)
    (unary_append_comm leftCarrier rightCarrier))

theorem FilterPrincipalSuffix_unary_intersection_zero_result_absurd
    {base left right meet leftPoint rightPoint z : BHist} :
    UnaryHistory base -> UnaryHistory left -> UnaryHistory right -> Cont left right meet ->
      Cont base left leftPoint -> Cont base right rightPoint ->
        Cont base meet (BHist.e0 z) -> False := by
  intro baseCarrier leftCarrier rightCarrier leftRight _baseLeft _baseRight baseMeet
  have meetCarrier : UnaryHistory meet := unary_cont_closed leftCarrier rightCarrier leftRight
  have resultCarrier : UnaryHistory (BHist.e0 z) :=
    unary_cont_closed baseCarrier meetCarrier baseMeet
  exact unary_no_zero_extension resultCarrier

theorem FilterPrincipalEmptyCarrier_semanticNameCert :
    SemanticNameCert (fun h : BHist => UnaryHistory h ∧ hsame h BHist.Empty)
      (fun h : BHist => UnaryHistory h ∧ hsame h BHist.Empty)
      (fun h : BHist => UnaryHistory h ∧ hsame h BHist.Empty) hsame := by
  constructor
  · constructor
    · exact Exists.intro BHist.Empty (And.intro unary_empty (hsame_refl BHist.Empty))
    · intro h _carrier
      exact hsame_refl h
    · intro h k same
      exact hsame_symm same
    · intro h k r sameHK sameKR
      exact hsame_trans sameHK sameKR
    · intro h k same carrier
      exact And.intro (unary_transport carrier.left same)
        (hsame_trans (hsame_symm same) carrier.right)
  · intro h source
    exact source
  · intro h source
    exact source

end BEDC.Derived.FilterUp
