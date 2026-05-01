import BEDC.Derived.OptionUp.TaggedPayload

namespace BEDC.Derived.OptionUp

open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert

def TaggedOptionMapRel (S T : BHist → Prop) {RelS RelT : BHist → BHist → Prop}
    (delta : DescentCertificate BHist BHist RelS RelT) (h k : BHist) : Prop :=
  (hsame h BHist.Empty ∧ hsame k BHist.Empty) ∨
    ∃ a : BHist,
      S a ∧ T (delta.map a) ∧ hsame h (BHist.e1 a) ∧
        hsame k (BHist.e1 (delta.map a))

theorem TaggedOptionMapRel_preserves_classification {S T : BHist → Prop}
    {RelS RelT : BHist → BHist → Prop}
    (delta : DescentCertificate BHist BHist RelS RelT)
    (cert : NameCert S RelS)
    (source_hsame : TaggedOptionSourceHsameCompatible S RelS)
    {h h' k k' : BHist} :
    TaggedOptionHistoryClassifier S RelS h h' →
      TaggedOptionMapRel S T delta h k →
        TaggedOptionMapRel S T delta h' k' →
          TaggedOptionHistoryClassifier T RelT k k' := by
  intro sourceClass mapH mapH'
  cases sourceClass with
  | inl sourceAbsent =>
      cases mapH with
      | inl mapAbsentH =>
          cases mapH' with
          | inl mapAbsentH' =>
              exact Or.inl (And.intro mapAbsentH.right mapAbsentH'.right)
          | inr mapPresentH' =>
              cases mapPresentH' with
              | intro a' dataH' =>
                  cases dataH' with
                  | intro _ restH' =>
                      cases restH' with
                      | intro _ restH' =>
                          cases restH' with
                          | intro sameH'Present _ =>
                              exact False.elim
                                (not_hsame_emp_e1
                                  (hsame_trans (hsame_symm sourceAbsent.right)
                                    sameH'Present))
      | inr mapPresentH =>
          cases mapPresentH with
          | intro a dataH =>
              cases dataH with
              | intro _ restH =>
                  cases restH with
                  | intro _ restH =>
                      cases restH with
                      | intro sameHPresent _ =>
                          exact False.elim
                            (not_hsame_emp_e1
                              (hsame_trans (hsame_symm sourceAbsent.left) sameHPresent))
  | inr sourcePresent =>
      cases sourcePresent with
      | intro a sourceRest =>
          cases sourceRest with
          | intro b sourceData =>
              cases sourceData with
              | intro sourceA sourceRest =>
                  cases sourceRest with
                  | intro sourceB sourceRest =>
                      cases sourceRest with
                      | intro sameHPresent sourceRest =>
                          cases sourceRest with
                          | intro sameH'Present relAB =>
                              cases mapH with
                              | inl mapAbsentH =>
                                  exact False.elim
                                    (not_hsame_emp_e1
                                      (hsame_trans (hsame_symm mapAbsentH.left)
                                        sameHPresent))
                              | inr mapPresentH =>
                                  cases mapPresentH with
                                  | intro a0 dataH =>
                                      cases dataH with
                                      | intro sourceA0 restH =>
                                          cases restH with
                                          | intro targetA0 restH =>
                                              cases restH with
                                              | intro sameHMap sameKMap =>
                                                  cases mapH' with
                                                  | inl mapAbsentH' =>
                                                      exact False.elim
                                                        (not_hsame_emp_e1
                                                          (hsame_trans
                                                            (hsame_symm mapAbsentH'.left)
                                                            sameH'Present))
                                                  | inr mapPresentH' =>
                                                      cases mapPresentH' with
                                                      | intro b0 dataH' =>
                                                          cases dataH' with
                                                          | intro sourceB0 restH' =>
                                                              cases restH' with
                                                              | intro targetB0 restH' =>
                                                                  cases restH' with
                                                                  | intro sameH'Map sameK'Map =>
                                                                      have sameA0A :
                                                                          hsame a0 a :=
                                                                        hsame_e1_iff.mp
                                                                          (hsame_trans
                                                                            (hsame_symm
                                                                              sameHMap)
                                                                            sameHPresent)
                                                                      have sameBB0 :
                                                                          hsame b b0 :=
                                                                        hsame_e1_iff.mp
                                                                          (hsame_trans
                                                                            (hsame_symm
                                                                              sameH'Present)
                                                                            sameH'Map)
                                                                      have relA0A : RelS a0 a :=
                                                                        source_hsame sourceA0
                                                                          sourceA sameA0A
                                                                      have relBB0 : RelS b b0 :=
                                                                        source_hsame sourceB
                                                                          sourceB0 sameBB0
                                                                      have relA0B : RelS a0 b :=
                                                                        NameCert.equiv_trans
                                                                          cert relA0A relAB
                                                                      have relA0B0 : RelS a0 b0 :=
                                                                        NameCert.equiv_trans
                                                                          cert relA0B relBB0
                                                                      exact Or.inr
                                                                        (Exists.intro
                                                                          (delta.map a0)
                                                                          (Exists.intro
                                                                            (delta.map b0)
                                                                            (And.intro targetA0
                                                                              (And.intro
                                                                                targetB0
                                                                                (And.intro
                                                                                  sameKMap
                                                                                  (And.intro
                                                                                    sameK'Map
                                                                                    (delta.respects
                                                                                      relA0B0)))))))

theorem TaggedOptionMapRel_common_source_target_classification {S T : BHist -> Prop}
    {RelS RelT : BHist -> BHist -> Prop}
    (delta : DescentCertificate BHist BHist RelS RelT)
    (source_hsame : TaggedOptionSourceHsameCompatible S RelS) {h k k' : BHist} :
    TaggedOptionMapRel S T delta h k ->
      TaggedOptionMapRel S T delta h k' ->
        TaggedOptionHistoryClassifier T RelT k k' := by
  intro mapK mapK'
  cases mapK with
  | inl absentK =>
      cases mapK' with
      | inl absentK' =>
          exact Or.inl (And.intro absentK.right absentK'.right)
      | inr presentK' =>
          cases presentK' with
          | intro b dataK' =>
              cases dataK' with
              | intro _ restK' =>
                  cases restK' with
                  | intro _ restK' =>
                      cases restK' with
                      | intro sameHPresent _ =>
                          exact False.elim
                            (not_hsame_emp_e1
                              (hsame_trans (hsame_symm absentK.left) sameHPresent))
  | inr presentK =>
      cases presentK with
      | intro a dataK =>
          cases dataK with
          | intro sourceA restK =>
              cases restK with
              | intro targetA restK =>
                  cases restK with
                  | intro sameHPresentA sameKPresentA =>
                      cases mapK' with
                      | inl absentK' =>
                          exact False.elim
                            (not_hsame_emp_e1
                              (hsame_trans (hsame_symm absentK'.left) sameHPresentA))
                      | inr presentK' =>
                          cases presentK' with
                          | intro b dataK' =>
                              cases dataK' with
                              | intro sourceB restK' =>
                                  cases restK' with
                                  | intro targetB restK' =>
                                      cases restK' with
                                      | intro sameHPresentB sameK'PresentB =>
                                          have sameAB : hsame a b :=
                                            hsame_e1_iff.mp
                                              (hsame_trans
                                                (hsame_symm sameHPresentA)
                                                sameHPresentB)
                                          have relAB : RelS a b :=
                                            source_hsame sourceA sourceB sameAB
                                          exact Or.inr
                                            (Exists.intro (delta.map a)
                                              (Exists.intro (delta.map b)
                                                (And.intro targetA
                                                  (And.intro targetB
                                                    (And.intro sameKPresentA
                                                      (And.intro sameK'PresentB
                                                        (delta.respects relAB)))))))

end BEDC.Derived.OptionUp
