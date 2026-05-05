import BEDC.Derived.RealUp.Readback

namespace BEDC.Derived.RealUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Cont
open BEDC.FKernel.Unary
open BEDC.Derived.RatUp
open BEDC.Derived.StreamNameUp

def MalformedRealSealedDenom (h : BHist) : Prop :=
  hsame h (BHist.e1 BHist.Empty) ∨
    (exists t : BHist, hsame h (BHist.e1 (BHist.e0 t))) ∨
      (exists p z : BHist, hsame h (BHist.e1 (append p (BHist.e0 z))))

theorem RealConstant_appended_tail_bridge_malformed_sealed_denominator_exclusion
    {d e tailD tailE zD zE : BHist} {r q : BHist -> BHist} :
    let D := append d (BHist.e1 tailD)
    let E := append e (BHist.e1 tailE)
    (RatHistoryClassifier D E ->
        (MalformedRealSealedDenom (BHist.e1 D) -> False) ∧
          (MalformedRealSealedDenom (BHist.e1 E) -> False)) ∧
      (RatStreamNameClassifier (fun n : BHist => RatConstStream D (r n))
          (fun n : BHist => RatConstStream E (q n)) ->
        (MalformedRealSealedDenom (BHist.e1 D) -> False) ∧
          (MalformedRealSealedDenom (BHist.e1 E) -> False)) ∧
      (RealUnaryStreamClassifier (fun n : BHist => RatConstStream D (r n))
          (fun n : BHist => RatConstStream E (q n)) ->
        (MalformedRealSealedDenom (BHist.e1 D) -> False) ∧
          (MalformedRealSealedDenom (BHist.e1 E) -> False)) ∧
      (RealConstantHistoryClassifier (BHist.e1 D) (BHist.e1 E) ->
        (MalformedRealSealedDenom (BHist.e1 D) -> False) ∧
          (MalformedRealSealedDenom (BHist.e1 E) -> False)) := by
  dsimp
  let D := append d (BHist.e1 tailD)
  let E := append e (BHist.e1 tailE)
  have rows :=
    RealConstant_appended_tail_bridge_denominator_package
      (d := d) (e := e) (tailD := tailD) (tailE := tailE) (zD := zD) (zE := zE)
      (r := r) (q := q)
  dsimp at rows
  have fromPositiveD :
      PositiveUnaryDenominator D -> MalformedRealSealedDenom (BHist.e1 D) -> False := by
    intro positive malformed
    cases malformed with
    | inl sameEmpty =>
        exact PositiveUnaryDenominator_not_empty positive (hsame_e1_iff.mp sameEmpty)
    | inr rest =>
        cases rest with
        | inl oneZero =>
            cases oneZero with
            | intro t sameZero =>
                exact PositiveUnaryDenominator_e0_absurd
                  (PositiveUnaryDenominator_hsame_transport (hsame_e1_iff.mp sameZero)
                    positive)
        | inr appendedZero =>
            cases appendedZero with
            | intro p appendedZero =>
                cases appendedZero with
                | intro z sameAppend =>
                    exact PositiveUnaryDenominator_append_e0_tail_absurd
                      (PositiveUnaryDenominator_hsame_transport
                        (hsame_e1_iff.mp sameAppend) positive)
  have fromPositiveE :
      PositiveUnaryDenominator E -> MalformedRealSealedDenom (BHist.e1 E) -> False := by
    intro positive malformed
    cases malformed with
    | inl sameEmpty =>
        exact PositiveUnaryDenominator_not_empty positive (hsame_e1_iff.mp sameEmpty)
    | inr rest =>
        cases rest with
        | inl oneZero =>
            cases oneZero with
            | intro t sameZero =>
                exact PositiveUnaryDenominator_e0_absurd
                  (PositiveUnaryDenominator_hsame_transport (hsame_e1_iff.mp sameZero)
                    positive)
        | inr appendedZero =>
            cases appendedZero with
            | intro p appendedZero =>
                cases appendedZero with
                | intro z sameAppend =>
                    exact PositiveUnaryDenominator_append_e0_tail_absurd
                      (PositiveUnaryDenominator_hsame_transport
                        (hsame_e1_iff.mp sameAppend) positive)
  have fromPackage :
      RatHistoryClassifier D E ∧ PositiveUnaryDenominator D ∧
        PositiveUnaryDenominator E ∧ UnaryHistory d ∧ UnaryHistory tailD ∧
          UnaryHistory e ∧ UnaryHistory tailE ∧ (hsame D BHist.Empty -> False) ∧
            (hsame E BHist.Empty -> False) ∧ (hsame D (BHist.e0 zD) -> False) ∧
              (hsame E (BHist.e0 zE) -> False) ∧ hsame D E ->
        (MalformedRealSealedDenom (BHist.e1 D) -> False) ∧
          (MalformedRealSealedDenom (BHist.e1 E) -> False) := by
    intro package
    exact And.intro (fromPositiveD package.right.left)
      (fromPositiveE package.right.right.left)
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

end BEDC.Derived.RealUp
