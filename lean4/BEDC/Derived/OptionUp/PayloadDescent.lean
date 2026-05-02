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

def TaggedOptionDescentComp {RelS RelT RelU : BHist → BHist → Prop}
    (delta : DescentCertificate BHist BHist RelS RelT)
    (epsilon : DescentCertificate BHist BHist RelT RelU) :
    DescentCertificate BHist BHist RelS RelU :=
  { map := fun a => epsilon.map (delta.map a)
    respects := by
      intro _a _b same
      exact epsilon.respects (delta.respects same) }

theorem TaggedOptionMapRel_composition_closed {S T U : BHist → Prop}
    {RelS RelT RelU : BHist → BHist → Prop}
    (delta : DescentCertificate BHist BHist RelS RelT)
    (epsilon : DescentCertificate BHist BHist RelT RelU)
    (rhoE : ∀ b : BHist, T b → U (epsilon.map b))
    (epsilon_hsame :
      ∀ x y : BHist, T x → T y → hsame x y → hsame (epsilon.map x) (epsilon.map y))
    {h k m : BHist} :
    TaggedOptionMapRel S T delta h k →
      TaggedOptionMapRel T U epsilon k m →
        TaggedOptionMapRel S U (TaggedOptionDescentComp delta epsilon) h m := by
  intro deltaRel epsilonRel
  cases deltaRel with
  | inl deltaAbsent =>
      cases epsilonRel with
      | inl epsilonAbsent =>
          exact Or.inl (And.intro deltaAbsent.left epsilonAbsent.right)
      | inr epsilonPresent =>
          cases epsilonPresent with
          | intro b data =>
              cases data with
              | intro _targetB rest =>
                  cases rest with
                  | intro _targetEpsilonB rest =>
                      cases rest with
                      | intro sameKPresent _sameMPresent =>
                          exact False.elim
                            (not_hsame_emp_e1
                              (hsame_trans (hsame_symm deltaAbsent.right) sameKPresent))
  | inr deltaPresent =>
      cases deltaPresent with
      | intro a data =>
          cases data with
          | intro sourceA rest =>
              cases rest with
              | intro targetDeltaA rest =>
                  cases rest with
                  | intro sameHPresent sameKDelta =>
                      cases epsilonRel with
                      | inl epsilonAbsent =>
                          exact False.elim
                            (not_hsame_e1_empty
                              (hsame_trans (hsame_symm sameKDelta) epsilonAbsent.left))
                      | inr epsilonPresent =>
                          cases epsilonPresent with
                          | intro b dataB =>
                              cases dataB with
                              | intro targetB restB =>
                                  cases restB with
                                  | intro _targetEpsilonB restB =>
                                      cases restB with
                                      | intro sameKB sameMPresent =>
                                          have sameDeltaB : hsame (delta.map a) b :=
                                            hsame_e1_iff.mp
                                              (hsame_trans (hsame_symm sameKDelta) sameKB)
                                          have sameEpsilon :
                                              hsame (epsilon.map (delta.map a)) (epsilon.map b) :=
                                            epsilon_hsame (delta.map a) b targetDeltaA targetB
                                              sameDeltaB
                                          exact Or.inr
                                            (Exists.intro a
                                              (And.intro sourceA
                                                (And.intro (rhoE (delta.map a) targetDeltaA)
                                                  (And.intro sameHPresent
                                                    (hsame_trans sameMPresent
                                                      (hsame_symm
                                                        (hsame_e1_congr sameEpsilon)))))))

theorem TaggedOptionMapRel_composition_visible_payload_readback {S T U : BHist -> Prop}
    {RelS RelT RelU : BHist -> BHist -> Prop}
    (delta : DescentCertificate BHist BHist RelS RelT)
    (epsilon : DescentCertificate BHist BHist RelT RelU) {h k m a c : BHist} :
    TaggedOptionMapRel S T delta h k -> TaggedOptionMapRel T U epsilon k m ->
      S a -> hsame h (BHist.e1 a) -> U c -> hsame m (BHist.e1 c) ->
        hsame c (epsilon.map (delta.map a)) := by
  intro deltaRel epsilonRel _sourceA sameHA _targetC sameMC
  cases deltaRel with
  | inl deltaAbsent =>
      exact False.elim
        (not_hsame_emp_e1 (hsame_trans (hsame_symm deltaAbsent.left) sameHA))
  | inr deltaPresent =>
      cases deltaPresent with
      | intro a0 data =>
          cases data with
          | intro _sourceA0 rest =>
              cases rest with
              | intro _targetDeltaA0 rest =>
                  cases rest with
                  | intro sameHPresent sameKDelta =>
                      have sameA0A : hsame a0 a :=
                        hsame_e1_iff.mp (hsame_trans (hsame_symm sameHPresent) sameHA)
                      cases sameA0A
                      cases epsilonRel with
                      | inl epsilonAbsent =>
                          exact False.elim
                            (not_hsame_e1_empty
                              (hsame_trans (hsame_symm sameKDelta) epsilonAbsent.left))
                      | inr epsilonPresent =>
                          cases epsilonPresent with
                          | intro b dataB =>
                              cases dataB with
                              | intro _targetB restB =>
                                  cases restB with
                                  | intro _targetEpsilonB restB =>
                                      cases restB with
                                      | intro sameKB sameMPresent =>
                                          have sameDeltaB : hsame (delta.map a) b :=
                                            hsame_e1_iff.mp
                                              (hsame_trans (hsame_symm sameKDelta) sameKB)
                                          cases sameDeltaB
                                          exact
                                            hsame_e1_iff.mp
                                              (hsame_trans (hsame_symm sameMC) sameMPresent)

theorem TaggedOptionMapRel_composition_factorization_iff {S T U : BHist → Prop}
    {RelS RelT RelU : BHist → BHist → Prop}
    (delta : DescentCertificate BHist BHist RelS RelT)
    (epsilon : DescentCertificate BHist BHist RelT RelU)
    (rhoD : ∀ a : BHist, S a → T (delta.map a))
    (rhoE : ∀ b : BHist, T b → U (epsilon.map b))
    (epsilon_hsame :
      ∀ x y : BHist, T x → T y → hsame x y → hsame (epsilon.map x) (epsilon.map y))
    {h m : BHist} :
    TaggedOptionMapRel S U (TaggedOptionDescentComp delta epsilon) h m ↔
      ∃ k : BHist,
        TaggedOptionMapRel S T delta h k ∧ TaggedOptionMapRel T U epsilon k m := by
  constructor
  · intro compRel
    cases compRel with
    | inl absent =>
        exact Exists.intro BHist.Empty
          (And.intro
            (Or.inl (And.intro absent.left (hsame_refl BHist.Empty)))
            (Or.inl (And.intro (hsame_refl BHist.Empty) absent.right)))
    | inr present =>
        cases present with
        | intro a data =>
            cases data with
            | intro sourceA rest =>
                cases rest with
                | intro targetComp rest =>
                    cases rest with
                    | intro sameHPresent sameMPresent =>
                        exact Exists.intro (BHist.e1 (delta.map a))
                          (And.intro
                            (Or.inr
                              (Exists.intro a
                                (And.intro sourceA
                                  (And.intro (rhoD a sourceA)
                                    (And.intro sameHPresent
                                      (hsame_refl (BHist.e1 (delta.map a))))))))
                            (Or.inr
                              (Exists.intro (delta.map a)
                                (And.intro (rhoD a sourceA)
                                  (And.intro targetComp
                                    (And.intro (hsame_refl (BHist.e1 (delta.map a)))
                                      sameMPresent))))))
  · intro factorized
    cases factorized with
    | intro k data =>
        cases data with
        | intro deltaRel epsilonRel =>
            exact TaggedOptionMapRel_composition_closed delta epsilon rhoE epsilon_hsame
              deltaRel epsilonRel

theorem TaggedOptionMapRel_visible_branch_equivalence {S T : BHist -> Prop}
    {RelS RelT : BHist -> BHist -> Prop}
    (delta : DescentCertificate BHist BHist RelS RelT) {h k : BHist} :
    TaggedOptionMapRel S T delta h k ->
      (hsame h BHist.Empty <-> hsame k BHist.Empty) /\
        ((exists a : BHist, S a /\ hsame h (BHist.e1 a)) <->
          (exists b : BHist, T b /\ hsame k (BHist.e1 b))) := by
  intro mapRel
  constructor
  · constructor
    · intro sameHEmpty
      cases mapRel with
      | inl absent =>
          exact absent.right
      | inr present =>
          cases present with
          | intro a data =>
              cases data with
              | intro _ rest =>
                  cases rest with
                  | intro _ rest =>
                      cases rest with
                      | intro sameHPresent _ =>
                          exact False.elim
                            (not_hsame_e1_empty
                              (hsame_trans (hsame_symm sameHPresent) sameHEmpty))
    · intro sameKEmpty
      cases mapRel with
      | inl absent =>
          exact absent.left
      | inr present =>
          cases present with
          | intro a data =>
              cases data with
              | intro _ rest =>
                  cases rest with
                  | intro _ rest =>
                      cases rest with
                      | intro _ sameKPresent =>
                          exact False.elim
                            (not_hsame_e1_empty
                              (hsame_trans (hsame_symm sameKPresent) sameKEmpty))
  · constructor
    · intro presentH
      cases mapRel with
      | inl absent =>
          cases presentH with
          | intro a data =>
              cases data with
              | intro _ sameHPresent =>
                  exact False.elim
                    (not_hsame_emp_e1 (hsame_trans (hsame_symm absent.left) sameHPresent))
      | inr present =>
          cases present with
          | intro a data =>
              cases data with
              | intro _ rest =>
                  cases rest with
                  | intro targetA rest =>
                      cases rest with
                      | intro _ sameKPresent =>
                          exact Exists.intro (delta.map a)
                            (And.intro targetA sameKPresent)
    · intro presentK
      cases mapRel with
      | inl absent =>
          cases presentK with
          | intro b data =>
              cases data with
              | intro _ sameKPresent =>
                  exact False.elim
                    (not_hsame_emp_e1 (hsame_trans (hsame_symm absent.right) sameKPresent))
      | inr present =>
          cases present with
          | intro a data =>
              cases data with
              | intro sourceA rest =>
                  cases rest with
                  | intro _ rest =>
                      cases rest with
                      | intro sameHPresent _ =>
                          exact Exists.intro a (And.intro sourceA sameHPresent)

theorem TaggedOptionMapRel_total_carrier_transport {S T : BHist -> Prop}
    {RelS RelT : BHist -> BHist -> Prop}
    (delta : DescentCertificate BHist BHist RelS RelT)
    (payload_transport : forall a : BHist, S a -> T (delta.map a)) {h : BHist} :
    TaggedOptionHistoryCarrier S h ->
      exists k : BHist, TaggedOptionMapRel S T delta h k /\ TaggedOptionHistoryCarrier T k := by
  intro carrier
  cases carrier with
  | inl absent =>
      exact Exists.intro BHist.Empty
        (And.intro
          (Or.inl (And.intro absent (hsame_refl BHist.Empty)))
          (Or.inl (hsame_refl BHist.Empty)))
  | inr present =>
      cases present with
      | intro a data =>
          cases data with
          | intro sourceA sameHPresent =>
              exact Exists.intro (BHist.e1 (delta.map a))
                (And.intro
                  (Or.inr
                    (Exists.intro a
                      (And.intro sourceA
                        (And.intro (payload_transport a sourceA)
                          (And.intro sameHPresent
                            (hsame_refl (BHist.e1 (delta.map a))))))))
                  (Or.inr
                    (Exists.intro (delta.map a)
                      (And.intro (payload_transport a sourceA)
                        (hsame_refl (BHist.e1 (delta.map a)))))))

def TaggedOptionPayloadDescentImageCarrier (S T : BHist → Prop)
    {RelS RelT : BHist → BHist → Prop}
    (delta : DescentCertificate BHist BHist RelS RelT) (k : BHist) : Prop :=
  ∃ h : BHist, TaggedOptionHistoryCarrier S h ∧ TaggedOptionMapRel S T delta h k

theorem TaggedOptionPayloadDescentImageCarrier_branch_exactness {S T : BHist → Prop}
    {RelS RelT : BHist → BHist → Prop}
    (delta : DescentCertificate BHist BHist RelS RelT) {k : BHist} :
    TaggedOptionPayloadDescentImageCarrier S T delta k ↔
      hsame k BHist.Empty ∨
        ∃ a : BHist, S a ∧ T (delta.map a) ∧ hsame k (BHist.e1 (delta.map a)) := by
  constructor
  · intro image
    cases image with
    | intro h imageData =>
        cases imageData with
        | intro _sourceCarrier mapRel =>
            cases mapRel with
            | inl absent =>
                exact Or.inl absent.right
            | inr present =>
                cases present with
                | intro a data =>
                    cases data with
                    | intro sourceA rest =>
                        cases rest with
                        | intro targetA rest =>
                            cases rest with
                            | intro _sameSource sameTarget =>
                                exact Or.inr
                                  (Exists.intro a
                                    (And.intro sourceA (And.intro targetA sameTarget)))
  · intro branch
    cases branch with
    | inl sameEmpty =>
        exact Exists.intro BHist.Empty
          (And.intro (Or.inl (hsame_refl BHist.Empty))
            (Or.inl (And.intro (hsame_refl BHist.Empty) sameEmpty)))
    | inr present =>
        cases present with
        | intro a data =>
            cases data with
            | intro sourceA rest =>
                cases rest with
                | intro targetA sameTarget =>
                    exact Exists.intro (BHist.e1 a)
                      (And.intro
                        (Or.inr
                          (Exists.intro a
                            (And.intro sourceA (hsame_refl (BHist.e1 a)))))
                        (Or.inr
                          (Exists.intro a
                            (And.intro sourceA
                              (And.intro targetA
                                (And.intro (hsame_refl (BHist.e1 a)) sameTarget))))))

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
