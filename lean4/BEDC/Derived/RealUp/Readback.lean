import BEDC.Derived.RealUp.Core
import BEDC.Derived.RealUp.ConstantStreamBridge
import BEDC.Derived.RatUp.DenominatorAppendDecomposition

namespace BEDC.Derived.RealUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Cont
open BEDC.FKernel.Unary
open BEDC.Derived.RatUp
open BEDC.Derived.StreamNameUp

theorem RealStreamClassifier_transport_selected_e1_pair_readback
    {x x' y y' : Nat -> BHist} {n : Nat} {a b : BHist} :
    (forall i : Nat, hsame (x i) (x' i)) ->
      (forall i : Nat, hsame (y i) (y' i)) ->
        RealStreamClassifier x y ->
          hsame (x' n) (BHist.e1 a) ->
            hsame (y' n) (BHist.e1 b) ->
              UnaryHistory a ∧ UnaryHistory b ∧ hsame a b := by
  intro sameX sameY classified sameLeft sameRight
  have hPrefix : RealStreamPrefixClassifier x y n :=
    (RealStreamClassifier_finite_prefix_exactness.mp classified) n
  have transported : RealStreamPrefixClassifier x' y' n :=
    RealStreamPrefixClassifier_hsame_transport sameX sameY n hPrefix
  exact RealStreamPrefixClassifier_e1_pair_readback transported sameLeft sameRight

theorem RealConstantHistoryClassifier_append_e1_tail_unary_readback
    {d e tailD tailE : BHist} :
    RealConstantHistoryClassifier (BHist.e1 (append d (BHist.e1 tailD)))
      (BHist.e1 (append e (BHist.e1 tailE))) ->
      UnaryHistory d ∧ UnaryHistory tailD ∧ UnaryHistory e ∧ UnaryHistory tailE ∧
        hsame (append d (BHist.e1 tailD)) (append e (BHist.e1 tailE)) := by
  intro classified
  have rational :
      RatHistoryClassifier (append d (BHist.e1 tailD)) (append e (BHist.e1 tailE)) :=
    RealConstantHistoryClassifier_e1_iff_rat.mp classified
  have positives := RatHistoryClassifier_positive_denominators rational
  have leftUnary :=
    PositiveUnaryDenominator_append_e1_right_iff.mp positives.left
  have rightUnary :=
    PositiveUnaryDenominator_append_e1_right_iff.mp positives.right
  exact And.intro leftUnary.left
    (And.intro leftUnary.right
      (And.intro rightUnary.left (And.intro rightUnary.right rational.right.right)))

theorem RealConstantHistoryClassifier_append_e1_tail_denominator_package
    {d e tailD tailE zD zE : BHist} :
    RealConstantHistoryClassifier (BHist.e1 (append d (BHist.e1 tailD)))
      (BHist.e1 (append e (BHist.e1 tailE))) ->
      RatHistoryClassifier (append d (BHist.e1 tailD)) (append e (BHist.e1 tailE)) ∧
        PositiveUnaryDenominator (append d (BHist.e1 tailD)) ∧
          PositiveUnaryDenominator (append e (BHist.e1 tailE)) ∧ UnaryHistory d ∧
            UnaryHistory tailD ∧ UnaryHistory e ∧ UnaryHistory tailE ∧
              (hsame (append d (BHist.e1 tailD)) BHist.Empty -> False) ∧
                (hsame (append e (BHist.e1 tailE)) BHist.Empty -> False) ∧
                  (hsame (append d (BHist.e1 tailD)) (BHist.e0 zD) -> False) ∧
                    (hsame (append e (BHist.e1 tailE)) (BHist.e0 zE) -> False) ∧
                      hsame (append d (BHist.e1 tailD)) (append e (BHist.e1 tailE)) := by
  intro classified
  have rational :
      RatHistoryClassifier (append d (BHist.e1 tailD)) (append e (BHist.e1 tailE)) :=
    RealConstantHistoryClassifier_e1_iff_rat.mp classified
  have positives :
      PositiveUnaryDenominator (append d (BHist.e1 tailD)) ∧
        PositiveUnaryDenominator (append e (BHist.e1 tailE)) :=
    RatHistoryClassifier_positive_denominators rational
  have leftUnary :
      UnaryHistory d ∧ UnaryHistory tailD :=
    PositiveUnaryDenominator_append_e1_right_iff.mp positives.left
  have rightUnary :
      UnaryHistory e ∧ UnaryHistory tailE :=
    PositiveUnaryDenominator_append_e1_right_iff.mp positives.right
  have leftNotEmpty :
      hsame (append d (BHist.e1 tailD)) BHist.Empty -> False :=
    PositiveUnaryDenominator_not_empty positives.left
  have rightNotEmpty :
      hsame (append e (BHist.e1 tailE)) BHist.Empty -> False :=
    PositiveUnaryDenominator_not_empty positives.right
  have leftNotE0 :
      hsame (append d (BHist.e1 tailD)) (BHist.e0 zD) -> False := by
    intro sameZero
    exact PositiveUnaryDenominator_e0_absurd
      (PositiveUnaryDenominator_hsame_transport sameZero positives.left)
  have rightNotE0 :
      hsame (append e (BHist.e1 tailE)) (BHist.e0 zE) -> False := by
    intro sameZero
    exact PositiveUnaryDenominator_e0_absurd
      (PositiveUnaryDenominator_hsame_transport sameZero positives.right)
  exact And.intro rational
    (And.intro positives.left
      (And.intro positives.right
        (And.intro leftUnary.left
          (And.intro leftUnary.right
            (And.intro rightUnary.left
              (And.intro rightUnary.right
                (And.intro leftNotEmpty
                  (And.intro rightNotEmpty
                    (And.intro leftNotE0
                      (And.intro rightNotE0 rational.right.right))))))))))

theorem RealConstant_appended_tail_bridge_denominator_package
    {d e tailD tailE zD zE : BHist} {r q : BHist -> BHist} :
    let D := append d (BHist.e1 tailD)
    let E := append e (BHist.e1 tailE)
    (RatHistoryClassifier D E ->
        RatHistoryClassifier D E ∧ PositiveUnaryDenominator D ∧
          PositiveUnaryDenominator E ∧ UnaryHistory d ∧ UnaryHistory tailD ∧
            UnaryHistory e ∧ UnaryHistory tailE ∧ (hsame D BHist.Empty -> False) ∧
              (hsame E BHist.Empty -> False) ∧ (hsame D (BHist.e0 zD) -> False) ∧
                (hsame E (BHist.e0 zE) -> False) ∧ hsame D E) ∧
      (RatStreamNameClassifier (fun n : BHist => RatConstStream D (r n))
          (fun n : BHist => RatConstStream E (q n)) ->
        RatHistoryClassifier D E ∧ PositiveUnaryDenominator D ∧
          PositiveUnaryDenominator E ∧ UnaryHistory d ∧ UnaryHistory tailD ∧
            UnaryHistory e ∧ UnaryHistory tailE ∧ (hsame D BHist.Empty -> False) ∧
              (hsame E BHist.Empty -> False) ∧ (hsame D (BHist.e0 zD) -> False) ∧
                (hsame E (BHist.e0 zE) -> False) ∧ hsame D E) ∧
      (RealUnaryStreamClassifier (fun n : BHist => RatConstStream D (r n))
          (fun n : BHist => RatConstStream E (q n)) ->
        RatHistoryClassifier D E ∧ PositiveUnaryDenominator D ∧
          PositiveUnaryDenominator E ∧ UnaryHistory d ∧ UnaryHistory tailD ∧
            UnaryHistory e ∧ UnaryHistory tailE ∧ (hsame D BHist.Empty -> False) ∧
              (hsame E BHist.Empty -> False) ∧ (hsame D (BHist.e0 zD) -> False) ∧
                (hsame E (BHist.e0 zE) -> False) ∧ hsame D E) ∧
      (RealConstantHistoryClassifier (BHist.e1 D) (BHist.e1 E) ->
        RatHistoryClassifier D E ∧ PositiveUnaryDenominator D ∧
          PositiveUnaryDenominator E ∧ UnaryHistory d ∧ UnaryHistory tailD ∧
            UnaryHistory e ∧ UnaryHistory tailE ∧ (hsame D BHist.Empty -> False) ∧
              (hsame E BHist.Empty -> False) ∧ (hsame D (BHist.e0 zD) -> False) ∧
                (hsame E (BHist.e0 zE) -> False) ∧ hsame D E) := by
  dsimp
  let D := append d (BHist.e1 tailD)
  let E := append e (BHist.e1 tailE)
  have fromReal :
      RealConstantHistoryClassifier (BHist.e1 D) (BHist.e1 E) ->
        RatHistoryClassifier D E ∧ PositiveUnaryDenominator D ∧
          PositiveUnaryDenominator E ∧ UnaryHistory d ∧ UnaryHistory tailD ∧
            UnaryHistory e ∧ UnaryHistory tailE ∧ (hsame D BHist.Empty -> False) ∧
              (hsame E BHist.Empty -> False) ∧ (hsame D (BHist.e0 zD) -> False) ∧
                (hsame E (BHist.e0 zE) -> False) ∧ hsame D E := by
    intro classified
    exact RealConstantHistoryClassifier_append_e1_tail_denominator_package
      (d := d) (e := e) (tailD := tailD) (tailE := tailE) (zD := zD) (zE := zE)
      classified
  constructor
  · intro classified
    exact fromReal (RealConstantHistoryClassifier_e1_iff_rat.mpr classified)
  · constructor
    · intro classified
      have atEmpty := classified.right.right BHist.Empty unary_empty
      change RatHistoryClassifier D E at atEmpty
      exact fromReal (RealConstantHistoryClassifier_e1_iff_rat.mpr atEmpty)
    · constructor
      · intro classified
        have atEmpty := classified BHist.Empty unary_empty
        change RatHistoryClassifier D E at atEmpty
        exact fromReal (RealConstantHistoryClassifier_e1_iff_rat.mpr atEmpty)
      · intro classified
        exact fromReal classified

theorem RealConstant_appended_tail_bridge_appended_e0_tail_absurd
    {d e tailD tailE uD uE zD zE : BHist} {r q : BHist -> BHist} :
    let D := append d (BHist.e1 tailD)
    let E := append e (BHist.e1 tailE)
    (RatHistoryClassifier D E ->
        (hsame D (append uD (BHist.e0 zD)) -> False) ∧
          (hsame E (append uE (BHist.e0 zE)) -> False)) ∧
      (RatStreamNameClassifier (fun n : BHist => RatConstStream D (r n))
          (fun n : BHist => RatConstStream E (q n)) ->
        (hsame D (append uD (BHist.e0 zD)) -> False) ∧
          (hsame E (append uE (BHist.e0 zE)) -> False)) ∧
      (RealUnaryStreamClassifier (fun n : BHist => RatConstStream D (r n))
          (fun n : BHist => RatConstStream E (q n)) ->
        (hsame D (append uD (BHist.e0 zD)) -> False) ∧
          (hsame E (append uE (BHist.e0 zE)) -> False)) ∧
      (RealConstantHistoryClassifier (BHist.e1 D) (BHist.e1 E) ->
        (hsame D (append uD (BHist.e0 zD)) -> False) ∧
          (hsame E (append uE (BHist.e0 zE)) -> False)) := by
  dsimp
  let D := append d (BHist.e1 tailD)
  let E := append e (BHist.e1 tailE)
  have rows :=
    RealConstant_appended_tail_bridge_denominator_package
      (d := d) (e := e) (tailD := tailD) (tailE := tailE) (zD := zD) (zE := zE)
      (r := r) (q := q)
  dsimp at rows
  have fromPackage :
      RatHistoryClassifier D E ∧ PositiveUnaryDenominator D ∧
        PositiveUnaryDenominator E ∧ UnaryHistory d ∧ UnaryHistory tailD ∧
          UnaryHistory e ∧ UnaryHistory tailE ∧ (hsame D BHist.Empty -> False) ∧
            (hsame E BHist.Empty -> False) ∧ (hsame D (BHist.e0 zD) -> False) ∧
              (hsame E (BHist.e0 zE) -> False) ∧ hsame D E ->
        (hsame D (append uD (BHist.e0 zD)) -> False) ∧
          (hsame E (append uE (BHist.e0 zE)) -> False) := by
    intro package
    constructor
    · intro displayed
      exact PositiveUnaryDenominator_append_e0_tail_absurd
        (PositiveUnaryDenominator_hsame_transport displayed package.right.left)
    · intro displayed
      exact PositiveUnaryDenominator_append_e0_tail_absurd
        (PositiveUnaryDenominator_hsame_transport displayed package.right.right.left)
  constructor
  · intro classified
    exact fromPackage (rows.left classified)
  · constructor
    · intro classified
      exact fromPackage (rows.right.left classified)
    · constructor
      · intro classified
        exact fromPackage (rows.right.right.left classified)
      · intro classified
        exact fromPackage (rows.right.right.right classified)

theorem RealConstant_appended_tail_bridge_denominator_package_exactness
    {d e tailD tailE zD zE : BHist} {r q : BHist -> BHist} :
    let D := append d (BHist.e1 tailD)
    let E := append e (BHist.e1 tailE)
    (RatHistoryClassifier D E ∧ PositiveUnaryDenominator D ∧ PositiveUnaryDenominator E ∧
      UnaryHistory d ∧ UnaryHistory tailD ∧ UnaryHistory e ∧ UnaryHistory tailE ∧
        (hsame D BHist.Empty -> False) ∧ (hsame E BHist.Empty -> False) ∧
          (hsame D (BHist.e0 zD) -> False) ∧ (hsame E (BHist.e0 zE) -> False) ∧
            hsame D E) ↔
      RatHistoryClassifier D E ∧
        RatStreamNameClassifier (fun n : BHist => RatConstStream D (r n))
          (fun n : BHist => RatConstStream E (q n)) ∧
          RealUnaryStreamClassifier (fun n : BHist => RatConstStream D (r n))
            (fun n : BHist => RatConstStream E (q n)) ∧
            RealConstantHistoryClassifier (BHist.e1 D) (BHist.e1 E) := by
  dsimp
  let D := append d (BHist.e1 tailD)
  let E := append e (BHist.e1 tailE)
  constructor
  · intro package
    have streamName :
        RatStreamNameClassifier (fun n : BHist => RatConstStream D (r n))
          (fun n : BHist => RatConstStream E (q n)) :=
      And.intro
        (Iff.mp (RealConstantStreamCarrier_reindexed_streamName_bridge
          (d := D) (r := r)).left package.left.left)
        (And.intro
          (Iff.mp (RealConstantStreamCarrier_reindexed_streamName_bridge
            (d := E) (r := q)).left package.left.right.left)
          (fun _n _nUnary => package.left))
    have unaryStream :
        RealUnaryStreamClassifier (fun n : BHist => RatConstStream D (r n))
          (fun n : BHist => RatConstStream E (q n)) :=
      fun _n _nUnary => package.left
    have constantHistory :
        RealConstantHistoryClassifier (BHist.e1 D) (BHist.e1 E) :=
      Iff.mpr RealConstantHistoryClassifier_e1_iff_rat package.left
    exact And.intro package.left (And.intro streamName (And.intro unaryStream constantHistory))
  · intro rows
    exact (RealConstant_appended_tail_bridge_denominator_package
      (d := d) (e := e) (tailD := tailD) (tailE := tailE) (zD := zD) (zE := zE)
      (r := r) (q := q)).right.right.right rows.right.right.right

theorem RealConstant_appended_tail_bridge_full_denominator_tail_package
    {d e tailD tailE uD uE zD zE : BHist} {r q : BHist -> BHist} :
    let D := append d (BHist.e1 tailD)
    let E := append e (BHist.e1 tailE)
    let FullPackage : Prop :=
      RatHistoryClassifier D E ∧ PositiveUnaryDenominator D ∧ PositiveUnaryDenominator E ∧
        UnaryHistory d ∧ UnaryHistory tailD ∧ UnaryHistory e ∧ UnaryHistory tailE ∧
          (hsame D BHist.Empty -> False) ∧ (hsame E BHist.Empty -> False) ∧
            (hsame D (BHist.e0 zD) -> False) ∧ (hsame E (BHist.e0 zE) -> False) ∧
              hsame D E ∧ (hsame D (append uD (BHist.e0 zD)) -> False) ∧
                (hsame E (append uE (BHist.e0 zE)) -> False) ∧ hsame d e
    hsame tailD tailE ->
      (RatHistoryClassifier D E -> FullPackage) ∧
      (RatStreamNameClassifier (fun n : BHist => RatConstStream D (r n))
        (fun n : BHist => RatConstStream E (q n)) -> FullPackage) ∧
      (RealUnaryStreamClassifier (fun n : BHist => RatConstStream D (r n))
        (fun n : BHist => RatConstStream E (q n)) -> FullPackage) ∧
      (RealConstantHistoryClassifier (BHist.e1 D) (BHist.e1 E) -> FullPackage) := by
  dsimp
  intro sameTail
  cases sameTail
  have rows :=
    RealConstant_appended_tail_bridge_denominator_package
      (d := d) (e := e) (tailD := tailD) (tailE := tailD) (zD := zD) (zE := zE)
      (r := r) (q := q)
  dsimp at rows
  have extend :
      RatHistoryClassifier (append d (BHist.e1 tailD)) (append e (BHist.e1 tailD)) ∧
        PositiveUnaryDenominator (append d (BHist.e1 tailD)) ∧
          PositiveUnaryDenominator (append e (BHist.e1 tailD)) ∧ UnaryHistory d ∧
            UnaryHistory tailD ∧ UnaryHistory e ∧ UnaryHistory tailD ∧
              (hsame (append d (BHist.e1 tailD)) BHist.Empty -> False) ∧
                (hsame (append e (BHist.e1 tailD)) BHist.Empty -> False) ∧
                  (hsame (append d (BHist.e1 tailD)) (BHist.e0 zD) -> False) ∧
                    (hsame (append e (BHist.e1 tailD)) (BHist.e0 zE) -> False) ∧
                      hsame (append d (BHist.e1 tailD)) (append e (BHist.e1 tailD)) ->
        RatHistoryClassifier (append d (BHist.e1 tailD)) (append e (BHist.e1 tailD)) ∧
          PositiveUnaryDenominator (append d (BHist.e1 tailD)) ∧
            PositiveUnaryDenominator (append e (BHist.e1 tailD)) ∧ UnaryHistory d ∧
              UnaryHistory tailD ∧ UnaryHistory e ∧ UnaryHistory tailD ∧
                (hsame (append d (BHist.e1 tailD)) BHist.Empty -> False) ∧
                  (hsame (append e (BHist.e1 tailD)) BHist.Empty -> False) ∧
                    (hsame (append d (BHist.e1 tailD)) (BHist.e0 zD) -> False) ∧
                      (hsame (append e (BHist.e1 tailD)) (BHist.e0 zE) -> False) ∧
                        hsame (append d (BHist.e1 tailD)) (append e (BHist.e1 tailD)) ∧
                          (hsame (append d (BHist.e1 tailD))
                              (append uD (BHist.e0 zD)) ->
                            False) ∧
                            (hsame (append e (BHist.e1 tailD))
                                (append uE (BHist.e0 zE)) ->
                              False) ∧ hsame d e := by
    intro package
    cases package with
    | intro rat rest =>
        cases rest with
        | intro positiveD rest =>
            cases rest with
            | intro positiveE rest =>
                cases rest with
                | intro unaryD rest =>
                    cases rest with
                    | intro unaryTailD rest =>
                        cases rest with
                        | intro unaryE rest =>
                            cases rest with
                            | intro unaryTailE rest =>
                                cases rest with
                                | intro notDEmpty rest =>
                                    cases rest with
                                    | intro notEEmpty rest =>
                                        cases rest with
                                        | intro notDE0 rest =>
                                            cases rest with
                                            | intro notEE0 sameDEFull =>
                                                have notDAppendE0 :
                                                    hsame (append d (BHist.e1 tailD))
                                                        (append uD (BHist.e0 zD)) ->
                                                      False := by
                                                  intro sameZero
                                                  exact PositiveUnaryDenominator_append_e0_tail_absurd
                                                    (PositiveUnaryDenominator_hsame_transport
                                                      sameZero positiveD)
                                                have notEAppendE0 :
                                                    hsame (append e (BHist.e1 tailD))
                                                        (append uE (BHist.e0 zE)) ->
                                                      False := by
                                                  intro sameZero
                                                  exact PositiveUnaryDenominator_append_e0_tail_absurd
                                                    (PositiveUnaryDenominator_hsame_transport
                                                      sameZero positiveE)
                                                have sameDE : hsame d e :=
                                                  append_right_cancel (k := BHist.e1 tailD)
                                                    sameDEFull
                                                exact ⟨rat, positiveD, positiveE, unaryD,
                                                  unaryTailD, unaryE, unaryTailE, notDEmpty,
                                                  notEEmpty, notDE0, notEE0, sameDEFull,
                                                  notDAppendE0, notEAppendE0, sameDE⟩
  constructor
  · intro classified
    exact extend (rows.left classified)
  · constructor
    · intro classified
      exact extend (rows.right.left classified)
    · constructor
      · intro classified
        exact extend (rows.right.right.left classified)
      · intro classified
        exact extend (rows.right.right.right classified)

theorem RealConstant_appended_tail_bridge_full_denominator_tail_package_exactness
    {d e tailD tailE uD uE zD zE : BHist} {r q : BHist -> BHist} :
    let D := append d (BHist.e1 tailD)
    let E := append e (BHist.e1 tailE)
    let FullPackage : Prop :=
      RatHistoryClassifier D E ∧ PositiveUnaryDenominator D ∧ PositiveUnaryDenominator E ∧
        UnaryHistory d ∧ UnaryHistory tailD ∧ UnaryHistory e ∧ UnaryHistory tailE ∧
          (hsame D BHist.Empty -> False) ∧ (hsame E BHist.Empty -> False) ∧
            (hsame D (BHist.e0 zD) -> False) ∧ (hsame E (BHist.e0 zE) -> False) ∧
              hsame D E ∧ (hsame D (append uD (BHist.e0 zD)) -> False) ∧
                (hsame E (append uE (BHist.e0 zE)) -> False) ∧ hsame d e
    hsame tailD tailE ->
      (FullPackage ↔
        RatHistoryClassifier D E ∧
          RatStreamNameClassifier (fun n : BHist => RatConstStream D (r n))
            (fun n : BHist => RatConstStream E (q n)) ∧
            RealUnaryStreamClassifier (fun n : BHist => RatConstStream D (r n))
              (fun n : BHist => RatConstStream E (q n)) ∧
              RealConstantHistoryClassifier (BHist.e1 D) (BHist.e1 E)) := by
  dsimp
  intro sameTail
  constructor
  · intro fullPackage
    have denominatorPackage :
        RatHistoryClassifier (append d (BHist.e1 tailD)) (append e (BHist.e1 tailE)) ∧
          PositiveUnaryDenominator (append d (BHist.e1 tailD)) ∧
            PositiveUnaryDenominator (append e (BHist.e1 tailE)) ∧ UnaryHistory d ∧
              UnaryHistory tailD ∧ UnaryHistory e ∧ UnaryHistory tailE ∧
                (hsame (append d (BHist.e1 tailD)) BHist.Empty -> False) ∧
                  (hsame (append e (BHist.e1 tailE)) BHist.Empty -> False) ∧
                    (hsame (append d (BHist.e1 tailD)) (BHist.e0 zD) -> False) ∧
                      (hsame (append e (BHist.e1 tailE)) (BHist.e0 zE) -> False) ∧
                        hsame (append d (BHist.e1 tailD)) (append e (BHist.e1 tailE)) := by
      exact ⟨fullPackage.left, fullPackage.right.left, fullPackage.right.right.left,
        fullPackage.right.right.right.left, fullPackage.right.right.right.right.left,
        fullPackage.right.right.right.right.right.left,
        fullPackage.right.right.right.right.right.right.left,
        fullPackage.right.right.right.right.right.right.right.left,
        fullPackage.right.right.right.right.right.right.right.right.left,
        fullPackage.right.right.right.right.right.right.right.right.right.left,
        fullPackage.right.right.right.right.right.right.right.right.right.right.left,
        fullPackage.right.right.right.right.right.right.right.right.right.right.right.left⟩
    exact (RealConstant_appended_tail_bridge_denominator_package_exactness
      (d := d) (e := e) (tailD := tailD) (tailE := tailE) (zD := zD) (zE := zE)
      (r := r) (q := q)).mp denominatorPackage
  · intro rows
    have fullRows :=
      RealConstant_appended_tail_bridge_full_denominator_tail_package
        (d := d) (e := e) (tailD := tailD) (tailE := tailE) (uD := uD) (uE := uE)
        (zD := zD) (zE := zE) (r := r) (q := q) sameTail
    exact fullRows.left rows.left

theorem RealConstantHistoryClassifier_append_common_head_e1_tail_readback
    {left d e tailD tailE : BHist} :
    RealConstantHistoryClassifier (BHist.e1 (append left (append d (BHist.e1 tailD))))
      (BHist.e1 (append left (append e (BHist.e1 tailE)))) ->
      hsame tailD tailE ->
        UnaryHistory left ∧ UnaryHistory d ∧ UnaryHistory e ∧ UnaryHistory tailD ∧
          UnaryHistory tailE ∧ hsame d e := by
  intro classified sameTail
  have leftAssoc :
      hsame (BHist.e1 (append left (append d (BHist.e1 tailD))))
        (BHist.e1 (append (append left d) (BHist.e1 tailD))) := by
    exact congrArg BHist.e1 (append_assoc left d (BHist.e1 tailD)).symm
  have rightAssoc :
      hsame (BHist.e1 (append left (append e (BHist.e1 tailE))))
        (BHist.e1 (append (append left e) (BHist.e1 tailE))) := by
    exact congrArg BHist.e1 (append_assoc left e (BHist.e1 tailE)).symm
  have displayed :
      RealConstantHistoryClassifier (BHist.e1 (append (append left d) (BHist.e1 tailD)))
        (BHist.e1 (append (append left e) (BHist.e1 tailE))) :=
    RealConstantHistoryClassifier_endpoint_transport leftAssoc rightAssoc classified
  have readback :=
    RealConstantHistoryClassifier_append_e1_tail_unary_readback displayed
  have leftFactors :
      UnaryHistory left ∧ UnaryHistory d :=
    unary_append_factors_iff_result.mpr readback.left
  have rightFactors :
      UnaryHistory left ∧ UnaryHistory e :=
    unary_append_factors_iff_result.mpr readback.right.right.left
  have sameHeaded : hsame (append left d) (append left e) := by
    cases sameTail
    exact append_right_cancel (k := BHist.e1 tailD) readback.right.right.right.right
  have sameDE : hsame d e :=
    append_left_cancel (h := left) sameHeaded
  exact And.intro leftFactors.left
    (And.intro leftFactors.right
      (And.intro rightFactors.right
        (And.intro readback.right.left
          (And.intro readback.right.right.right.left sameDE))))

theorem RealConstantHistoryClassifier_append_e1_matched_tail_head_readback
    {d e tailD tailE : BHist} :
    RealConstantHistoryClassifier (BHist.e1 (append d (BHist.e1 tailD)))
      (BHist.e1 (append e (BHist.e1 tailE))) ->
      hsame tailD tailE ->
        UnaryHistory d ∧ UnaryHistory tailD ∧ UnaryHistory e ∧ UnaryHistory tailE ∧
          hsame d e := by
  intro classified sameTail
  have readback :=
    RealConstantHistoryClassifier_append_e1_tail_unary_readback classified
  cases sameTail
  have sameDE : hsame d e :=
    append_right_cancel (k := BHist.e1 tailD) readback.right.right.right.right
  exact And.intro readback.left
    (And.intro readback.right.left
      (And.intro readback.right.right.left
        (And.intro readback.right.right.right.left sameDE)))

theorem RealStreamClassifier_selected_append_e1_tail_hsame_cancel
    {x y : Nat -> BHist} {n : Nat} {d e tailD tailE : BHist} :
    RealStreamClassifier x y ->
      hsame (x n) (BHist.e1 (append d (BHist.e1 tailD))) ->
        hsame (y n) (BHist.e1 (append e (BHist.e1 tailE))) ->
          hsame tailD tailE -> hsame d e := by
  intro classified sameLeft sameRight sameTail
  have pointClassified : RatHistoryClassifier (x n) (y n) :=
    classified n
  have displayed :
      RatHistoryClassifier (BHist.e1 (append d (BHist.e1 tailD)))
        (BHist.e1 (append e (BHist.e1 tailE))) :=
    RatHistoryClassifier_hsame_transport sameLeft sameRight pointClassified
  have readback :
      UnaryHistory (append d (BHist.e1 tailD)) ∧
        UnaryHistory (append e (BHist.e1 tailE)) ∧
          hsame (append d (BHist.e1 tailD)) (append e (BHist.e1 tailE)) :=
    RatHistoryClassifier_e1_tail_unary_iff.mp displayed
  cases sameTail
  exact append_right_cancel (k := BHist.e1 tailD) readback.right.right

theorem RealConstant_appended_tail_bridge_head_tail_agreement_iff
    {d e tailD tailE zD zE : BHist} {r q : BHist -> BHist} :
    let D := append d (BHist.e1 tailD)
    let E := append e (BHist.e1 tailE)
    (RatHistoryClassifier D E -> (hsame d e ↔ hsame tailD tailE)) ∧
      (RatStreamNameClassifier (fun n : BHist => RatConstStream D (r n))
          (fun n : BHist => RatConstStream E (q n)) ->
        (hsame d e ↔ hsame tailD tailE)) ∧
      (RealUnaryStreamClassifier (fun n : BHist => RatConstStream D (r n))
          (fun n : BHist => RatConstStream E (q n)) ->
        (hsame d e ↔ hsame tailD tailE)) ∧
      (RealConstantHistoryClassifier (BHist.e1 D) (BHist.e1 E) ->
        (hsame d e ↔ hsame tailD tailE)) := by
  dsimp
  let D := append d (BHist.e1 tailD)
  let E := append e (BHist.e1 tailE)
  have rows :=
    RealConstant_appended_tail_bridge_denominator_package
      (d := d) (e := e) (tailD := tailD) (tailE := tailE) (zD := zD) (zE := zE)
      (r := r) (q := q)
  dsimp at rows
  have packageSame :
      RatHistoryClassifier D E ∧ PositiveUnaryDenominator D ∧ PositiveUnaryDenominator E ∧
        UnaryHistory d ∧ UnaryHistory tailD ∧ UnaryHistory e ∧ UnaryHistory tailE ∧
          (hsame D BHist.Empty -> False) ∧ (hsame E BHist.Empty -> False) ∧
            (hsame D (BHist.e0 zD) -> False) ∧ (hsame E (BHist.e0 zE) -> False) ∧
              hsame D E ->
        hsame D E := by
    intro package
    exact package.right.right.right.right.right.right.right.right.right.right.right
  have fromSameDEFull : hsame D E -> (hsame d e ↔ hsame tailD tailE) := by
    intro sameFull
    constructor
    · intro sameHead
      cases sameHead
      exact hsame_e1_iff.mp (append_left_cancel (h := d) sameFull)
    · intro sameTail
      cases sameTail
      exact append_right_cancel (k := BHist.e1 tailD) sameFull
  constructor
  · intro classified
    exact fromSameDEFull (packageSame (rows.left classified))
  · constructor
    · intro classified
      exact fromSameDEFull (packageSame (rows.right.left classified))
    · constructor
      · intro classified
        exact fromSameDEFull (packageSame (rows.right.right.left classified))
      · intro classified
        exact fromSameDEFull (packageSame (rows.right.right.right classified))

end BEDC.Derived.RealUp
