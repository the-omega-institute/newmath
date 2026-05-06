import BEDC.Derived.ComplexTopologyUp

namespace BEDC.Derived.ComplexTopologyUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Cont
open BEDC.FKernel.Unary

def ComplexTopologyCertifiedSubradius (inner outer tail : BHist) : Prop :=
  UnaryHistory inner ∧ UnaryHistory outer ∧ UnaryHistory tail ∧ Cont inner tail outer

theorem ComplexTopologyOpenDiskGap_certified_subradius_extension
    {center rSmall rLarge point gap tail gapLarge : BHist} :
    ComplexTopologyOpenDiskGap center rSmall point gap ->
      ComplexTopologyCertifiedSubradius rSmall rLarge tail -> Cont gap tail gapLarge ->
        ComplexTopologyOpenDiskGap center rLarge point gapLarge ∧ Cont point gapLarge rLarge := by
  intro disk subradius gapTail
  exact ComplexTopologyOpenDiskGap_radius_extension_closed disk subradius.right.right.left
    subradius.right.right.right gapTail

theorem ComplexTopologyCertifiedSubradius_comp {r0 r1 r2 e0 e1 e01 : BHist} :
    ComplexTopologyCertifiedSubradius r0 r1 e0 ->
      ComplexTopologyCertifiedSubradius r1 r2 e1 ->
        Cont e0 e1 e01 ->
          ComplexTopologyCertifiedSubradius r0 r2 e01 ∧ Cont r0 e01 r2 := by
  intro left right tailRel
  have e01Carrier : UnaryHistory e01 :=
    unary_cont_closed left.right.right.left right.right.right.left tailRel
  have radiusRel : Cont r0 e01 r2 := by
    apply cont_intro
    exact
      right.right.right.right.trans
        ((congrArg (fun h => append h e1) left.right.right.right).trans
          ((append_assoc r0 e0 e1).trans
            (congrArg (append r0) tailRel.symm)))
  exact
    And.intro
      (And.intro left.left
        (And.intro right.right.left
          (And.intro e01Carrier radiusRel)))
      radiusRel

theorem ComplexTopologyOpenDiskGap_subradius_inclusion
    {center inner outer point gap tail combined : BHist} :
    ComplexTopologyOpenDiskGap center inner point gap ->
      ComplexTopologyCertifiedSubradius inner outer tail ->
        Cont gap tail combined ->
          ComplexTopologyOpenDiskGap center outer point combined ∧
            Cont point combined outer := by
  intro disk subradius gapTail
  have combinedCarrier : UnaryHistory combined :=
    unary_cont_closed disk.right.right.right.left subradius.right.right.left gapTail
  have pointCombinedOuter : Cont point combined outer := by
    apply cont_intro
    exact
      subradius.right.right.right.trans
        ((congrArg (fun h => append h tail) disk.right.right.right.right).trans
          ((append_assoc point gap tail).trans
            (congrArg (append point) gapTail.symm)))
  exact
    And.intro
      (And.intro disk.left
        (And.intro subradius.right.left
          (And.intro disk.right.right.left
            (And.intro combinedCarrier pointCombinedOuter))))
      pointCombinedOuter

theorem ComplexTopologyOpenDiskGap_certified_subradius_public_readback
    {center inner outer point gap tail displayedGap : BHist} :
    ComplexTopologyCertifiedSubradius inner outer tail ->
      ComplexTopologyOpenDiskGap center inner point gap ->
        ComplexTopologyOpenDiskGap center outer point displayedGap ->
          hsame displayedGap (append gap tail) := by
  intro subradius smaller displayedOuter
  have extended :
      ComplexTopologyOpenDiskGap center outer point (append gap tail) ∧
        Cont point (append gap tail) outer :=
    ComplexTopologyOpenDiskGap_radius_extension_closed smaller subradius.right.right.left
      subradius.right.right.right (cont_intro rfl)
  exact ComplexTopologyOpenDiskGap_gap_deterministic displayedOuter extended.right

theorem ComplexTopologyOpenDiskGap_subradius_inclusion_readback
    {center inner outer point gap tail extendedGap : BHist} :
    ComplexTopologyOpenDiskGap center inner point gap ->
      ComplexTopologyCertifiedSubradius inner outer tail ->
        Cont gap tail extendedGap ->
          ComplexTopologyOpenDiskGap center outer point extendedGap ∧
            Cont point extendedGap outer ∧
              forall parentGap : BHist,
                ComplexTopologyOpenDiskGap center outer point parentGap ->
                  hsame parentGap extendedGap := by
  intro disk subradius gapTail
  have extended :
      ComplexTopologyOpenDiskGap center outer point extendedGap ∧
        Cont point extendedGap outer :=
    ComplexTopologyOpenDiskGap_radius_extension_closed disk subradius.right.right.left
      subradius.right.right.right gapTail
  exact And.intro extended.left
    (And.intro extended.right
      (fun parentGap parentDisk =>
        ComplexTopologyOpenDiskGap_gap_deterministic parentDisk extended.right))

theorem ComplexTopologyCertifiedSubradius_openDiskGap_extension_gap_readback
    {center inner outer point gap tail displayedGap : BHist} :
    ComplexTopologyOpenDiskGap center inner point gap ->
      ComplexTopologyCertifiedSubradius inner outer tail ->
        ComplexTopologyOpenDiskGap center outer point displayedGap ->
          hsame displayedGap (append gap tail) := by
  intro disk subradius displayed
  have gapStep : Cont gap tail (append gap tail) := by
    exact cont_intro rfl
  have extended :=
    ComplexTopologyOpenDiskGap_radius_extension_closed disk subradius.right.right.left
      subradius.right.right.right gapStep
  exact ComplexTopologyOpenDiskGap_gap_deterministic displayed extended.right

theorem ComplexTopologyCertifiedSubradius_open_disk_gap_public_readback
    {center inner outer point gap tail outerGap : BHist} :
    ComplexTopologyOpenDiskGap center inner point gap ->
      ComplexTopologyCertifiedSubradius inner outer tail ->
        Cont gap tail outerGap ->
          ComplexTopologyOpenDiskGap center outer point outerGap ∧
            Cont point outerGap outer ∧ hsame outerGap (append gap tail) := by
  intro disk subradius gapTail
  have outerGapUnary : UnaryHistory outerGap :=
    unary_cont_closed disk.right.right.right.left subradius.right.right.left gapTail
  have pointOuterGap : Cont point outerGap outer := by
    apply cont_intro
    exact
      subradius.right.right.right.trans
        ((congrArg (fun h => append h tail) disk.right.right.right.right).trans
          ((append_assoc point gap tail).trans
            (congrArg (append point) gapTail.symm)))
  exact
    And.intro
      (And.intro disk.left
        (And.intro subradius.right.left
          (And.intro disk.right.right.left
            (And.intro outerGapUnary pointOuterGap))))
      (And.intro pointOuterGap gapTail)

theorem ComplexTopologyOpenDiskGap_subradius_extension_public_readback
    {center inner outer point gap tail largeGap : BHist} :
    ComplexTopologyOpenDiskGap center inner point gap ->
      ComplexTopologyCertifiedSubradius inner outer tail ->
        Cont gap tail largeGap ->
          ComplexTopologyOpenDiskGap center outer point largeGap ∧ Cont point largeGap outer ∧
            hsame largeGap (append gap tail) := by
  intro disk subradius gapTail
  have largeGapCarrier : UnaryHistory largeGap :=
    unary_cont_closed disk.right.right.right.left subradius.right.right.left gapTail
  have pointLarge : Cont point largeGap outer := by
    apply cont_intro
    exact
      subradius.right.right.right.trans
        ((congrArg (fun h => append h tail) disk.right.right.right.right).trans
          ((append_assoc point gap tail).trans
            (congrArg (append point) gapTail.symm)))
  exact
    And.intro
      (And.intro disk.left
        (And.intro subradius.right.left
          (And.intro disk.right.right.left
            (And.intro largeGapCarrier pointLarge))))
      (And.intro pointLarge gapTail)

theorem ComplexTopologyCertifiedSubradius_nested_gap_readback
    {inner middle outer gap tail01 tail12 gapMiddle gapOuter composedTail directGap : BHist} :
    ComplexTopologyCertifiedSubradius inner middle tail01 ->
      ComplexTopologyCertifiedSubradius middle outer tail12 ->
        Cont tail01 tail12 composedTail ->
          Cont gap tail01 gapMiddle ->
            Cont gapMiddle tail12 gapOuter ->
              Cont gap composedTail directGap ->
                hsame gapOuter directGap ∧
                  hsame gapOuter (append gap (append tail01 tail12)) := by
  intro sub01 sub12 tailComp gapStep outerStep directStep
  have composedSubradius := ComplexTopologyCertifiedSubradius_comp sub01 sub12 tailComp
  have composedRadius : Cont inner composedTail outer := composedSubradius.right
  have composedCanonical : hsame composedTail (append tail01 tail12) :=
    cont_deterministic tailComp rfl
  have _outerReadback : hsame outer (append inner (append tail01 tail12)) :=
    hsame_trans (cont_deterministic composedRadius rfl)
      (congrArg (append inner) composedCanonical)
  have directCanonical : hsame directGap (append gap (append tail01 tail12)) :=
    hsame_trans (cont_deterministic directStep rfl)
      (congrArg (append gap) composedCanonical)
  have assocReadback : hsame gapOuter (append gap (append tail01 tail12)) := by
    cases gapStep
    cases outerStep
    exact append_assoc gap tail01 tail12
  exact And.intro (hsame_trans assocReadback (hsame_symm directCanonical)) assocReadback

end BEDC.Derived.ComplexTopologyUp
