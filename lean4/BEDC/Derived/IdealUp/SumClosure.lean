import BEDC.Derived.IdealUp

namespace BEDC.Derived.IdealUp

open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert

theorem IdealSum_ideal_closure_rows
    {Carrier I J : BHist -> Prop}
    {Classifier : BHist -> BHist -> Prop}
    {zero : BHist}
    {add mul : BHist -> BHist -> BHist}
    {neg : BHist -> BHist}
    (cert : NameCert Carrier Classifier)
    (carrierZero : Carrier zero)
    (carrierAdd : forall {x y : BHist}, Carrier x -> Carrier y -> Carrier (add x y))
    (carrierNeg : forall {x : BHist}, Carrier x -> Carrier (neg x))
    (carrierMul : forall {x y : BHist}, Carrier x -> Carrier y -> Carrier (mul x y))
    (I_support : forall {x : BHist}, I x -> Carrier x)
    (I_zero : I zero)
    (I_add : forall {x y : BHist}, I x -> I y -> I (add x y))
    (I_neg : forall {x : BHist}, I x -> I (neg x))
    (I_mul : forall {x y : BHist}, I x -> I y -> I (mul x y))
    (I_transport : forall {x y : BHist}, I x -> Classifier x y -> I y)
    (I_absorb : forall {r x : BHist}, Carrier r -> I x -> I (mul r x) ∧ I (mul x r))
    (J_support : forall {x : BHist}, J x -> Carrier x)
    (J_zero : J zero)
    (J_add : forall {x y : BHist}, J x -> J y -> J (add x y))
    (J_neg : forall {x : BHist}, J x -> J (neg x))
    (J_mul : forall {x y : BHist}, J x -> J y -> J (mul x y))
    (J_transport : forall {x y : BHist}, J x -> Classifier x y -> J y)
    (J_absorb : forall {r x : BHist}, Carrier r -> J x -> J (mul r x) ∧ J (mul x r))
    (zeroDecomp : Classifier zero (add zero zero))
    (addRegroup :
      forall {z w x y x' y' : BHist},
        Carrier z -> Carrier w -> Carrier x -> Carrier y -> Carrier x' -> Carrier y' ->
          Classifier z (add x y) -> Classifier w (add x' y') ->
            Classifier (add z w) (add (add x x') (add y y')))
    (negDistrib :
      forall {z x y : BHist},
        Carrier z -> Carrier x -> Carrier y -> Classifier z (add x y) ->
          Classifier (neg z) (add (neg x) (neg y)))
    (leftDistrib :
      forall {r z x y : BHist},
        Carrier r -> Carrier z -> Carrier x -> Carrier y -> Classifier z (add x y) ->
          Classifier (mul r z) (add (mul r x) (mul r y)))
    (rightDistrib :
      forall {r z x y : BHist},
        Carrier r -> Carrier z -> Carrier x -> Carrier y -> Classifier z (add x y) ->
          Classifier (mul z r) (add (mul x r) (mul y r))) :
    let IdealSum : BHist -> Prop :=
      fun z => exists x : BHist, exists y : BHist, I x ∧ J y ∧ Classifier z (add x y)
    (forall {z : BHist}, IdealSum z -> Carrier z) ∧
      IdealSum zero ∧
      (forall {z w : BHist}, IdealSum z -> IdealSum w -> IdealSum (add z w)) ∧
      (forall {z : BHist}, IdealSum z -> IdealSum (neg z)) ∧
      (forall {z w : BHist}, IdealSum z -> IdealSum w -> IdealSum (mul z w)) ∧
      (forall {z z' : BHist}, IdealSum z -> Classifier z z' -> IdealSum z') ∧
      (forall {r z : BHist}, Carrier r -> IdealSum z ->
        IdealSum (mul r z) ∧ IdealSum (mul z r)) := by
  dsimp
  have support :
      forall {z : BHist},
        (exists x : BHist, exists y : BHist, I x ∧ J y ∧ Classifier z (add x y)) ->
          Carrier z := by
    intro z sumZ
    cases sumZ with
    | intro x rest =>
        cases rest with
        | intro y rows =>
            have carrierX : Carrier x := I_support rows.left
            have carrierY : Carrier y := J_support rows.right.left
            have carrierXY : Carrier (add x y) := carrierAdd carrierX carrierY
            have sameBack : Classifier (add x y) z :=
              NameCert.equiv_symm cert rows.right.right
            exact NameCert.carrier_respects_equiv cert sameBack carrierXY
  constructor
  · intro z sumZ
    exact support sumZ
  · constructor
    · exact Exists.intro zero (Exists.intro zero ⟨I_zero, J_zero, zeroDecomp⟩)
    · constructor
      · intro z w sumZ sumW
        cases sumZ with
        | intro x restZ =>
            cases restZ with
            | intro y rowsZ =>
                cases sumW with
                | intro x' restW =>
                    cases restW with
                    | intro y' rowsW =>
                        have carrierZ : Carrier z := support
                          (Exists.intro x (Exists.intro y rowsZ))
                        have carrierW : Carrier w := support
                          (Exists.intro x' (Exists.intro y' rowsW))
                        have carrierX : Carrier x := I_support rowsZ.left
                        have carrierY : Carrier y := J_support rowsZ.right.left
                        have carrierX' : Carrier x' := I_support rowsW.left
                        have carrierY' : Carrier y' := J_support rowsW.right.left
                        exact Exists.intro (add x x') (Exists.intro (add y y')
                          ⟨I_add rowsZ.left rowsW.left, J_add rowsZ.right.left rowsW.right.left,
                            addRegroup carrierZ carrierW carrierX carrierY carrierX' carrierY'
                              rowsZ.right.right rowsW.right.right⟩)
      · constructor
        · intro z sumZ
          cases sumZ with
          | intro x rest =>
              cases rest with
              | intro y rows =>
                  have carrierZ : Carrier z := support (Exists.intro x (Exists.intro y rows))
                  have carrierX : Carrier x := I_support rows.left
                  have carrierY : Carrier y := J_support rows.right.left
                  exact Exists.intro (neg x) (Exists.intro (neg y)
                    ⟨I_neg rows.left, J_neg rows.right.left,
                      negDistrib carrierZ carrierX carrierY rows.right.right⟩)
        · constructor
          · intro z w sumZ sumW
            have carrierZ : Carrier z := support sumZ
            have productAbsorb :
                (exists x : BHist, exists y : BHist,
                  I x ∧ J y ∧ Classifier (mul z w) (add x y)) ∧
                (exists x : BHist, exists y : BHist,
                  I x ∧ J y ∧ Classifier (mul w z) (add x y)) := by
              cases sumW with
              | intro x rest =>
                  cases rest with
                  | intro y rows =>
                      have carrierW : Carrier w :=
                        support (Exists.intro x (Exists.intro y rows))
                      have carrierX : Carrier x := I_support rows.left
                      have carrierY : Carrier y := J_support rows.right.left
                      have iAbsorb : I (mul z x) ∧ I (mul x z) :=
                        I_absorb carrierZ rows.left
                      have jAbsorb : J (mul z y) ∧ J (mul y z) :=
                        J_absorb carrierZ rows.right.left
                      exact
                        ⟨Exists.intro (mul z x) (Exists.intro (mul z y)
                            ⟨iAbsorb.left, jAbsorb.left,
                              leftDistrib carrierZ carrierW carrierX carrierY
                                rows.right.right⟩),
                          Exists.intro (mul x z) (Exists.intro (mul y z)
                            ⟨iAbsorb.right, jAbsorb.right,
                              rightDistrib carrierZ carrierW carrierX carrierY
                                rows.right.right⟩)⟩
            exact productAbsorb.left
          · constructor
            · intro z z' sumZ sameZZ'
              cases sumZ with
              | intro x rest =>
                  cases rest with
                  | intro y rows =>
                      have sameZ'Z : Classifier z' z := NameCert.equiv_symm cert sameZZ'
                      have sameZ'XY : Classifier z' (add x y) :=
                        NameCert.equiv_trans cert sameZ'Z rows.right.right
                      exact Exists.intro x (Exists.intro y
                        ⟨rows.left, rows.right.left, sameZ'XY⟩)
            · intro r z carrierR sumZ
              cases sumZ with
              | intro x rest =>
                  cases rest with
                  | intro y rows =>
                      have carrierZ : Carrier z :=
                        support (Exists.intro x (Exists.intro y rows))
                      have carrierX : Carrier x := I_support rows.left
                      have carrierY : Carrier y := J_support rows.right.left
                      have iAbsorb : I (mul r x) ∧ I (mul x r) :=
                        I_absorb carrierR rows.left
                      have jAbsorb : J (mul r y) ∧ J (mul y r) :=
                        J_absorb carrierR rows.right.left
                      exact
                        ⟨Exists.intro (mul r x) (Exists.intro (mul r y)
                            ⟨iAbsorb.left, jAbsorb.left,
                              leftDistrib carrierR carrierZ carrierX carrierY
                                rows.right.right⟩),
                          Exists.intro (mul x r) (Exists.intro (mul y r)
                            ⟨iAbsorb.right, jAbsorb.right,
                              rightDistrib carrierR carrierZ carrierX carrierY
                                rows.right.right⟩)⟩

theorem IdealSumQuotientKernel_scope
    {Carrier I J : BHist -> Prop}
    {Classifier : BHist -> BHist -> Prop}
    {zero : BHist}
    {add sub : BHist -> BHist -> BHist}
    (cert : NameCert Carrier Classifier)
    (I_zero : I zero)
    (J_zero : J zero)
    (zeroDecomp : Classifier zero (add zero zero))
    (subDiagonal : forall {x : BHist}, Carrier x -> Classifier (sub x x) zero)
    (subCongr :
      forall {x x' y y' : BHist}, Classifier x x' -> Classifier y y' ->
        Classifier (sub x y) (sub x' y')) :
    (forall {x : BHist}, Carrier x ->
      Carrier x ∧ Carrier x ∧
        (exists i : BHist, exists j : BHist,
          I i ∧ J j ∧ Classifier (sub x x) (add i j))) ∧
      (forall {x y x' y' : BHist},
        Carrier x ∧ Carrier y ∧
          (exists i : BHist, exists j : BHist,
            I i ∧ J j ∧ Classifier (sub x y) (add i j)) ->
        Classifier x x' -> Classifier y y' ->
          Carrier x' ∧ Carrier y' ∧
            (exists i : BHist, exists j : BHist,
              I i ∧ J j ∧ Classifier (sub x' y') (add i j))) := by
  constructor
  · intro x carrierX
    have subToZero : Classifier (sub x x) zero :=
      subDiagonal carrierX
    have subToDecomp : Classifier (sub x x) (add zero zero) :=
      NameCert.equiv_trans cert subToZero zeroDecomp
    exact And.intro carrierX
      (And.intro carrierX
        (Exists.intro zero (Exists.intro zero
          (And.intro I_zero (And.intro J_zero subToDecomp)))))
  · intro x y x' y' rows sameXX' sameYY'
    have carrierX' : Carrier x' :=
      NameCert.carrier_respects_equiv cert sameXX' rows.left
    have carrierY' : Carrier y' :=
      NameCert.carrier_respects_equiv cert sameYY' rows.right.left
    cases rows.right.right with
    | intro i rest =>
        cases rest with
        | intro j decomp =>
            have sameSub : Classifier (sub x y) (sub x' y') :=
              subCongr sameXX' sameYY'
            have sameSubBack : Classifier (sub x' y') (sub x y) :=
              NameCert.equiv_symm cert sameSub
            have transported : Classifier (sub x' y') (add i j) :=
              NameCert.equiv_trans cert sameSubBack decomp.right.right
            exact And.intro carrierX'
              (And.intro carrierY'
                (Exists.intro i (Exists.intro j
                  (And.intro decomp.left (And.intro decomp.right.left transported)))))

end BEDC.Derived.IdealUp
