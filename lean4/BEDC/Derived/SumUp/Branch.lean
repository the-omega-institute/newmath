import BEDC.Derived.SumUp

namespace BEDC.Derived.SumUp

open BEDC.FKernel.Hist

theorem SumHistoryCarrier_visible_branch_exactness {Left Right : BHist → Prop}
    {h : BHist} :
    SumHistoryCarrier Left Right h ↔
      (∃ l : BHist, Left l ∧ hsame h (BHist.e0 l)) ∨
        (∃ r : BHist, Right r ∧ hsame h (BHist.e1 r)) := by
  constructor
  · intro carrier
    cases carrier with
    | inl leftBranch =>
        cases leftBranch with
        | intro l leftData =>
            cases leftData with
            | intro sameLeft leftCarrier =>
                exact Or.inl (Exists.intro l (And.intro leftCarrier sameLeft))
    | inr rightBranch =>
        cases rightBranch with
        | intro r rightData =>
            cases rightData with
            | intro sameRight rightCarrier =>
                exact Or.inr (Exists.intro r (And.intro rightCarrier sameRight))
  · intro branch
    cases branch with
    | inl leftBranch =>
        cases leftBranch with
        | intro l leftData =>
            cases leftData with
            | intro leftCarrier sameLeft =>
                exact Or.inl (Exists.intro l (And.intro sameLeft leftCarrier))
    | inr rightBranch =>
        cases rightBranch with
        | intro r rightData =>
            cases rightData with
            | intro rightCarrier sameRight =>
                exact Or.inr (Exists.intro r (And.intro sameRight rightCarrier))

theorem SumHistoryCarrier_empty_absurd {Left Right : BHist → Prop} :
    SumHistoryCarrier Left Right BHist.Empty → False := by
  intro carrier
  cases carrier with
  | inl leftBranch =>
      cases leftBranch with
      | intro l leftData =>
          exact not_hsame_emp_e0 leftData.left
  | inr rightBranch =>
      cases rightBranch with
      | intro r rightData =>
          exact not_hsame_emp_e1 rightData.left

theorem SumHistoryCarrier_visible_payload_determinism {Left Right : BHist → Prop}
    {h l l' r r' : BHist} :
    (hsame h (BHist.e0 l) → Left l → hsame h (BHist.e0 l') → Left l' → hsame l l') ∧
      (hsame h (BHist.e1 r) → Right r → hsame h (BHist.e1 r') → Right r' →
        hsame r r') := by
  constructor
  · intro sameLeft _ sameLeft' _
    exact hsame_e0_iff.mp (hsame_trans (hsame_symm sameLeft) sameLeft')
  · intro sameRight _ sameRight' _
    exact hsame_e1_iff.mp (hsame_trans (hsame_symm sameRight) sameRight')

theorem SumHistoryCarrier_branch_exclusivity {Left Right : BHist → Prop} {h : BHist} :
    ((∃ l : BHist, hsame h (BHist.e0 l) ∧ Left l) ∧
      (∃ r : BHist, hsame h (BHist.e1 r) ∧ Right r)) → False := by
  intro branches
  cases branches with
  | intro leftBranch rightBranch =>
      cases leftBranch with
      | intro l leftData =>
          cases leftData with
          | intro sameLeft _left =>
              cases rightBranch with
              | intro r rightData =>
                  cases rightData with
                  | intro sameRight _right =>
                      exact not_hsame_e0_e1
                        (hsame_trans (hsame_symm sameLeft) sameRight)

theorem SumHistoryCarrier_exclusive_visible_branch_partition {Left Right : BHist → Prop}
    {h : BHist} :
    SumHistoryCarrier Left Right h ↔
      (((∃ l : BHist, hsame h (BHist.e0 l) ∧ Left l) ∧
          ((∃ r : BHist, hsame h (BHist.e1 r) ∧ Right r) → False)) ∨
        ((∃ r : BHist, hsame h (BHist.e1 r) ∧ Right r) ∧
          ((∃ l : BHist, hsame h (BHist.e0 l) ∧ Left l) → False))) := by
  constructor
  · intro carrier
    cases carrier with
    | inl leftBranch =>
        exact Or.inl
          (And.intro leftBranch
            (fun rightBranch =>
              SumHistoryCarrier_branch_exclusivity (And.intro leftBranch rightBranch)))
    | inr rightBranch =>
        exact Or.inr
          (And.intro rightBranch
            (fun leftBranch =>
              SumHistoryCarrier_branch_exclusivity (And.intro leftBranch rightBranch)))
  · intro partition
    cases partition with
    | inl leftData =>
        exact Or.inl leftData.left
    | inr rightData =>
        exact Or.inr rightData.left

theorem SumHistoryCarrier_exclusive_visible_branch_partition_payload_first
    {Left Right : BHist → Prop} {h : BHist} :
    SumHistoryCarrier Left Right h ↔
      (((∃ l : BHist, Left l ∧ hsame h (BHist.e0 l)) ∧
          ((∃ r : BHist, Right r ∧ hsame h (BHist.e1 r)) → False)) ∨
        ((∃ r : BHist, Right r ∧ hsame h (BHist.e1 r)) ∧
          ((∃ l : BHist, Left l ∧ hsame h (BHist.e0 l)) → False))) := by
  constructor
  · intro carrier
    cases carrier with
    | inl leftBranch =>
        cases leftBranch with
        | intro l leftData =>
            cases leftData with
            | intro sameLeft leftCarrier =>
                exact Or.inl
                  (And.intro
                    (Exists.intro l (And.intro leftCarrier sameLeft))
                    (by
                      intro rightBranch
                      cases rightBranch with
                      | intro r rightData =>
                          cases rightData with
                          | intro _rightCarrier sameRight =>
                              exact not_hsame_e0_e1
                                (hsame_trans (hsame_symm sameLeft) sameRight)))
    | inr rightBranch =>
        cases rightBranch with
        | intro r rightData =>
            cases rightData with
            | intro sameRight rightCarrier =>
                exact Or.inr
                  (And.intro
                    (Exists.intro r (And.intro rightCarrier sameRight))
                    (by
                      intro leftBranch
                      cases leftBranch with
                      | intro l leftData =>
                          cases leftData with
                          | intro _leftCarrier sameLeft =>
                              exact not_hsame_e0_e1
                                (hsame_trans (hsame_symm sameLeft) sameRight)))
  · intro branch
    cases branch with
    | inl leftBranch =>
        cases leftBranch with
        | intro leftVisible _noRight =>
            cases leftVisible with
            | intro l leftData =>
                cases leftData with
                | intro leftCarrier sameLeft =>
                    exact Or.inl (Exists.intro l (And.intro sameLeft leftCarrier))
    | inr rightBranch =>
        cases rightBranch with
        | intro rightVisible _noLeft =>
            cases rightVisible with
            | intro r rightData =>
                cases rightData with
                | intro rightCarrier sameRight =>
                    exact Or.inr (Exists.intro r (And.intro sameRight rightCarrier))

theorem SumHistoryCarrier_single_valued_visible_readback {Left Right : BHist -> Prop}
    {h : BHist} :
    SumHistoryCarrier Left Right h ->
      (exists l : BHist,
        Left l /\ hsame h (BHist.e0 l) /\
          (forall l' : BHist, Left l' -> hsame h (BHist.e0 l') -> hsame l l') /\
            ((exists r : BHist, Right r /\ hsame h (BHist.e1 r)) -> False)) \/
        (exists r : BHist,
          Right r /\ hsame h (BHist.e1 r) /\
            (forall r' : BHist, Right r' -> hsame h (BHist.e1 r') -> hsame r r') /\
              ((exists l : BHist, Left l /\ hsame h (BHist.e0 l)) -> False)) := by
  intro carrier
  have partition :
      (((∃ l : BHist, Left l ∧ hsame h (BHist.e0 l)) ∧
          ((∃ r : BHist, Right r ∧ hsame h (BHist.e1 r)) → False)) ∨
        ((∃ r : BHist, Right r ∧ hsame h (BHist.e1 r)) ∧
          ((∃ l : BHist, Left l ∧ hsame h (BHist.e0 l)) → False))) :=
    Iff.mp SumHistoryCarrier_exclusive_visible_branch_partition_payload_first carrier
  cases partition with
  | inl leftBranch =>
      cases leftBranch with
      | intro leftVisible noRight =>
          cases leftVisible with
          | intro l leftData =>
              cases leftData with
              | intro leftCarrier sameLeft =>
                  exact Or.inl
                    (Exists.intro l
                      (And.intro leftCarrier
                        (And.intro sameLeft
                          (And.intro
                            (fun l' _leftCarrier' sameLeft' =>
                              hsame_e0_iff.mp (hsame_trans (hsame_symm sameLeft) sameLeft'))
                            noRight))))
  | inr rightBranch =>
      cases rightBranch with
      | intro rightVisible noLeft =>
          cases rightVisible with
          | intro r rightData =>
              cases rightData with
              | intro rightCarrier sameRight =>
                  exact Or.inr
                    (Exists.intro r
                        (And.intro rightCarrier
                          (And.intro sameRight
                            (And.intro
                              (fun r' _rightCarrier' sameRight' =>
                                hsame_e1_iff.mp
                                  (hsame_trans (hsame_symm sameRight) sameRight'))
                              noLeft))))

theorem SumHistoryCarrier_visible_tag_exactness {Left Right : BHist -> Prop} :
    (forall {l : BHist}, SumHistoryCarrier Left Right (BHist.e0 l) <->
      exists a : BHist, Left a /\ hsame l a) /\
      (forall {r : BHist}, SumHistoryCarrier Left Right (BHist.e1 r) <->
        exists b : BHist, Right b /\ hsame r b) := by
  constructor
  · intro l
    constructor
    · intro carrier
      have inverted : exists a : BHist, hsame l a /\ Left a :=
        SumHistoryCarrier_e0_inversion carrier
      cases inverted with
      | intro a data =>
          exact Exists.intro a (And.intro data.right data.left)
    · intro payload
      cases payload with
      | intro a data =>
          have tagged : SumHistoryCarrier Left Right (BHist.e0 a) :=
            SumHistoryCarrier_tagged_injections.left data.left
          exact SumHistoryCarrier_hsame_transport
            (hsame_e0_congr (hsame_symm data.right)) tagged
  · intro r
    constructor
    · intro carrier
      have inverted : exists b : BHist, hsame r b /\ Right b :=
        SumHistoryCarrier_e1_inversion carrier
      cases inverted with
      | intro b data =>
          exact Exists.intro b (And.intro data.right data.left)
    · intro payload
      cases payload with
      | intro b data =>
          have tagged : SumHistoryCarrier Left Right (BHist.e1 b) :=
            SumHistoryCarrier_tagged_injections.right data.left
          exact SumHistoryCarrier_hsame_transport
            (hsame_e1_congr (hsame_symm data.right)) tagged

theorem SumHistoryClassifier_carrier_aware_branch_partition {Left Right : BHist → Prop}
    {LeftEq RightEq : BHist → BHist → Prop} {h k : BHist} :
    SumHistoryCarrier Left Right h →
      SumHistoryCarrier Left Right k →
        SumHistoryClassifier Left Right LeftEq RightEq h k →
          (∃ a : BHist, ∃ b : BHist,
            Left a ∧ Left b ∧ hsame h (BHist.e0 a) ∧ hsame k (BHist.e0 b) ∧
              LeftEq a b) ∨
            (∃ a : BHist, ∃ b : BHist,
              Right a ∧ Right b ∧ hsame h (BHist.e1 a) ∧ hsame k (BHist.e1 b) ∧
                RightEq a b) := by
  intro carrierH carrierK classifier
  cases classifier with
  | inl leftBranch =>
      cases leftBranch with
      | intro a leftRest =>
          cases leftRest with
          | intro b data =>
              cases data with
              | intro sameH rest =>
                  cases rest with
                  | intro sameK sameLeft =>
                      have leftAtA :
                          ∃ a' : BHist, hsame a a' ∧ Left a' :=
                        SumHistoryCarrier_e0_inversion
                          (SumHistoryCarrier_hsame_transport sameH carrierH)
                      have leftAtB :
                          ∃ b' : BHist, hsame b b' ∧ Left b' :=
                        SumHistoryCarrier_e0_inversion
                          (SumHistoryCarrier_hsame_transport sameK carrierK)
                      cases leftAtA with
                      | intro a' leftDataA =>
                          cases leftDataA with
                          | intro sameA leftA' =>
                              cases sameA
                              cases leftAtB with
                              | intro b' leftDataB =>
                                  cases leftDataB with
                                  | intro sameB leftB' =>
                                      cases sameB
                                      exact Or.inl
                                        (Exists.intro a
                                          (Exists.intro b
                                            (And.intro leftA'
                                              (And.intro leftB'
                                                (And.intro sameH
                                                  (And.intro sameK sameLeft))))))
  | inr rightBranch =>
      cases rightBranch with
      | intro a rightRest =>
          cases rightRest with
          | intro b data =>
              cases data with
              | intro sameH rest =>
                  cases rest with
                  | intro sameK sameRight =>
                      have rightAtA :
                          ∃ a' : BHist, hsame a a' ∧ Right a' :=
                        SumHistoryCarrier_e1_inversion
                          (SumHistoryCarrier_hsame_transport sameH carrierH)
                      have rightAtB :
                          ∃ b' : BHist, hsame b b' ∧ Right b' :=
                        SumHistoryCarrier_e1_inversion
                          (SumHistoryCarrier_hsame_transport sameK carrierK)
                      cases rightAtA with
                      | intro a' rightDataA =>
                          cases rightDataA with
                          | intro sameA rightA' =>
                              cases sameA
                              cases rightAtB with
                              | intro b' rightDataB =>
                                  cases rightDataB with
                                  | intro sameB rightB' =>
                                      cases sameB
                                      exact Or.inr
                                        (Exists.intro a
                                          (Exists.intro b
                                            (And.intro rightA'
                                              (And.intro rightB'
                                                (And.intro sameH
                                                  (And.intro sameK sameRight))))))

theorem SumHistoryClassifier_carrier_aware_branch_exactness {Left Right : BHist → Prop}
    {LeftEq RightEq : BHist → BHist → Prop} {h k : BHist} :
    (SumHistoryCarrier Left Right h ∧ SumHistoryCarrier Left Right k ∧
        SumHistoryClassifier Left Right LeftEq RightEq h k) ↔
      ((∃ a : BHist, ∃ b : BHist,
          Left a ∧ Left b ∧ hsame h (BHist.e0 a) ∧ hsame k (BHist.e0 b) ∧
            LeftEq a b) ∨
        (∃ a : BHist, ∃ b : BHist,
          Right a ∧ Right b ∧ hsame h (BHist.e1 a) ∧ hsame k (BHist.e1 b) ∧
            RightEq a b)) := by
  constructor
  · intro packed
    cases packed with
    | intro carrierH rest =>
        cases rest with
        | intro carrierK classifier =>
            exact SumHistoryClassifier_carrier_aware_branch_partition carrierH carrierK classifier
  · intro branch
    cases branch with
    | inl leftBranch =>
        cases leftBranch with
        | intro a restA =>
            cases restA with
            | intro b data =>
                cases data with
                | intro leftA rest =>
                    cases rest with
                    | intro leftB rest =>
                        cases rest with
                        | intro sameH rest =>
                            cases rest with
                            | intro sameK leftEq =>
                                exact And.intro
                                  (Or.inl (Exists.intro a (And.intro sameH leftA)))
                                  (And.intro
                                    (Or.inl (Exists.intro b (And.intro sameK leftB)))
                                    (Or.inl
                                      (Exists.intro a
                                        (Exists.intro b
                                          (And.intro sameH (And.intro sameK leftEq))))))
    | inr rightBranch =>
        cases rightBranch with
        | intro a restA =>
            cases restA with
            | intro b data =>
                cases data with
                | intro rightA rest =>
                    cases rest with
                    | intro rightB rest =>
                        cases rest with
                        | intro sameH rest =>
                            cases rest with
                            | intro sameK rightEq =>
                                exact And.intro
                                  (Or.inr (Exists.intro a (And.intro sameH rightA)))
                                  (And.intro
                                    (Or.inr (Exists.intro b (And.intro sameK rightB)))
                                    (Or.inr
                                      (Exists.intro a
                                        (Exists.intro b
                                          (And.intro sameH (And.intro sameK rightEq))))))

theorem SumHistoryClassifier_branch_partition {Left Right : BHist → Prop}
    {LeftEq RightEq : BHist → BHist → Prop} {h k : BHist} :
    SumHistoryClassifier Left Right LeftEq RightEq h k →
      (∃ l l' : BHist,
        hsame h (BHist.e0 l) ∧ hsame k (BHist.e0 l') ∧ LeftEq l l') ∨
        (∃ r r' : BHist,
          hsame h (BHist.e1 r) ∧ hsame k (BHist.e1 r') ∧ RightEq r r') := by
  intro classifier
  cases classifier with
  | inl leftBranch =>
      cases leftBranch with
      | intro l rest =>
          cases rest with
          | intro l' data =>
              exact Or.inl (Exists.intro l (Exists.intro l' data))
  | inr rightBranch =>
      cases rightBranch with
      | intro r rest =>
          cases rest with
          | intro r' data =>
              exact Or.inr (Exists.intro r (Exists.intro r' data))

theorem SumHistorySource_weakening {Left Right Left' Right' : BHist -> Prop}
    {LeftEq RightEq LeftEq' RightEq' : BHist -> BHist -> Prop} :
    ((forall h : BHist, Left h -> Left' h) /\
        (forall h : BHist, Right h -> Right' h)) ->
      ((forall a b : BHist, LeftEq a b -> LeftEq' a b) /\
        (forall a b : BHist, RightEq a b -> RightEq' a b)) ->
        (forall {h : BHist},
          SumHistoryCarrier Left Right h -> SumHistoryCarrier Left' Right' h) /\
          (forall {h k : BHist},
            SumHistoryClassifier Left Right LeftEq RightEq h k ->
              SumHistoryClassifier Left' Right' LeftEq' RightEq' h k) := by
  intro sourceWeakening relationWeakening
  cases sourceWeakening with
  | intro leftSource rightSource =>
      cases relationWeakening with
      | intro leftRelation rightRelation =>
          constructor
          · intro h carrier
            cases carrier with
            | inl leftBranch =>
                cases leftBranch with
                | intro l data =>
                    cases data with
                    | intro sameH leftCarrier =>
                        exact Or.inl
                          (Exists.intro l (And.intro sameH (leftSource l leftCarrier)))
            | inr rightBranch =>
                cases rightBranch with
                | intro r data =>
                    cases data with
                    | intro sameH rightCarrier =>
                        exact Or.inr
                          (Exists.intro r (And.intro sameH (rightSource r rightCarrier)))
          · intro h k classifier
            cases classifier with
            | inl leftBranch =>
                cases leftBranch with
                | intro a restA =>
                    cases restA with
                    | intro b data =>
                        cases data with
                        | intro sameH rest =>
                            cases rest with
                            | intro sameK sameLeft =>
                                exact Or.inl
                                  (Exists.intro a
                                    (Exists.intro b
                                      (And.intro sameH
                                        (And.intro sameK
                                          (leftRelation a b sameLeft)))))
            | inr rightBranch =>
                cases rightBranch with
                | intro a restA =>
                    cases restA with
                    | intro b data =>
                        cases data with
                        | intro sameH rest =>
                            cases rest with
                            | intro sameK sameRight =>
                                exact Or.inr
                                  (Exists.intro a
                                    (Exists.intro b
                                      (And.intro sameH
                                        (And.intro sameK
                                          (rightRelation a b sameRight)))))

theorem SumHistoryClassifier_relation_weakening
    {Left Right LeftAlt RightAlt : BHist → Prop}
    {LeftEq RightEq LeftEq' RightEq' : BHist → BHist → Prop}
    (left_rel : ∀ {a b : BHist}, LeftEq a b → LeftEq' a b)
    (right_rel : ∀ {a b : BHist}, RightEq a b → RightEq' a b) {h k : BHist} :
    SumHistoryClassifier Left Right LeftEq RightEq h k →
      SumHistoryClassifier LeftAlt RightAlt LeftEq' RightEq' h k := by
  intro classifier
  cases classifier with
  | inl leftBranch =>
      cases leftBranch with
      | intro l restL =>
          cases restL with
          | intro l' data =>
              cases data with
              | intro sameH rest =>
                  cases rest with
                  | intro sameK sameLeft =>
                      exact Or.inl
                        (Exists.intro l
                          (Exists.intro l'
                            (And.intro sameH (And.intro sameK (left_rel sameLeft)))))
  | inr rightBranch =>
      cases rightBranch with
      | intro r restR =>
          cases restR with
          | intro r' data =>
              cases data with
              | intro sameH rest =>
                  cases rest with
                  | intro sameK sameRight =>
                      exact Or.inr
                        (Exists.intro r
                          (Exists.intro r'
                            (And.intro sameH (And.intro sameK (right_rel sameRight)))))

end BEDC.Derived.SumUp
