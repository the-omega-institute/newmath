import BEDC.Derived.RatUp

namespace BEDC.Derived.StreamNameUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Unary
open BEDC.Derived.RatUp

def RatStreamNameCarrier (s : BHist -> BHist) : Prop :=
  forall n : BHist, UnaryHistory n -> RatHistoryCarrier (s n)

def RatStreamNameClassifier (s t : BHist -> BHist) : Prop :=
  RatStreamNameCarrier s ∧ RatStreamNameCarrier t ∧
    forall n : BHist, UnaryHistory n -> RatHistoryClassifier (s n) (t n)

def RatConstStream (d : BHist) : BHist -> BHist
  | BHist.Empty => d
  | BHist.e0 _ => d
  | BHist.e1 _ => d

theorem RatStreamName_certificate_fields {s t u s' t' : BHist -> BHist} :
    RatStreamNameCarrier s ->
      RatStreamNameClassifier s t ->
        RatStreamNameClassifier t u ->
          (forall n : BHist, UnaryHistory n -> hsame (s n) (s' n)) ->
            (forall n : BHist, UnaryHistory n -> hsame (t n) (t' n)) ->
              RatStreamNameClassifier s s ∧
                RatStreamNameClassifier t s ∧
                  RatStreamNameClassifier s u ∧
                    (forall n : BHist, UnaryHistory n ->
                      RatHistoryCarrier (s n) ∧ RatHistoryCarrier (t n)) ∧
                      RatStreamNameClassifier s' t' := by
  intro carrierS classifiedST classifiedTU sameSS' sameTT'
  have carrierT : RatStreamNameCarrier t := classifiedST.right.left
  have carrierU : RatStreamNameCarrier u := classifiedTU.right.left
  have selfS : RatStreamNameClassifier s s := by
    exact And.intro carrierS
      (And.intro carrierS
        (fun n nUnary => And.intro (carrierS n nUnary)
          (And.intro (carrierS n nUnary) (hsame_refl (s n)))))
  have symmTS : RatStreamNameClassifier t s := by
    exact And.intro carrierT
      (And.intro carrierS
        (fun n nUnary => RatHistoryClassifier_symm (classifiedST.right.right n nUnary)))
  have transSU : RatStreamNameClassifier s u := by
    exact And.intro carrierS
      (And.intro carrierU
        (fun n nUnary =>
          RatHistoryClassifier_trans (classifiedST.right.right n nUnary)
            (classifiedTU.right.right n nUnary)))
  have endpointCarriers :
      forall n : BHist, UnaryHistory n -> RatHistoryCarrier (s n) ∧ RatHistoryCarrier (t n) := by
    intro n nUnary
    have point := classifiedST.right.right n nUnary
    exact And.intro point.left point.right.left
  have carrierS' : RatStreamNameCarrier s' := by
    intro n nUnary
    exact RatHistoryCarrier_hsame_transport (sameSS' n nUnary) (carrierS n nUnary)
  have carrierT' : RatStreamNameCarrier t' := by
    intro n nUnary
    exact RatHistoryCarrier_hsame_transport (sameTT' n nUnary) (carrierT n nUnary)
  have transportS'T' : RatStreamNameClassifier s' t' := by
    exact And.intro carrierS'
      (And.intro carrierT'
        (fun n nUnary =>
          RatHistoryClassifier_hsame_transport (sameSS' n nUnary) (sameTT' n nUnary)
            (classifiedST.right.right n nUnary)))
  exact And.intro selfS
    (And.intro symmTS
      (And.intro transSU
        (And.intro endpointCarriers transportS'T')))

theorem RatStreamName_constant_point_exactness {h k : BHist} :
    hsame (RatConstStream h BHist.Empty) h ∧ hsame (RatConstStream k BHist.Empty) k ∧
      ((RatStreamNameCarrier (RatConstStream h) ↔ RatHistoryCarrier h) ∧
        (RatStreamNameClassifier (RatConstStream h) (RatConstStream k) ↔
          RatHistoryClassifier h k)) := by
  have carrierH :
      RatStreamNameCarrier (RatConstStream h) ↔ RatHistoryCarrier h := by
    constructor
    · intro streamCarrier
      exact streamCarrier BHist.Empty unary_empty
    · intro ratCarrier n _nUnary
      cases n with
      | Empty => exact ratCarrier
      | e0 _ => exact ratCarrier
      | e1 _ => exact ratCarrier
  have carrierK :
      RatStreamNameCarrier (RatConstStream k) ↔ RatHistoryCarrier k := by
    constructor
    · intro streamCarrier
      exact streamCarrier BHist.Empty unary_empty
    · intro ratCarrier n _nUnary
      cases n with
      | Empty => exact ratCarrier
      | e0 _ => exact ratCarrier
      | e1 _ => exact ratCarrier
  have classifierHK :
      RatStreamNameClassifier (RatConstStream h) (RatConstStream k) ↔
        RatHistoryClassifier h k := by
    constructor
    · intro streamClassifier
      exact streamClassifier.right.right BHist.Empty unary_empty
    · intro ratClassifier
      exact And.intro (Iff.mpr carrierH ratClassifier.left)
        (And.intro (Iff.mpr carrierK ratClassifier.right.left)
          (fun n _nUnary => by
            cases n with
            | Empty => exact ratClassifier
            | e0 _ => exact ratClassifier
            | e1 _ => exact ratClassifier))
  exact And.intro (hsame_refl h)
    (And.intro (hsame_refl k) (And.intro carrierH classifierHK))

end BEDC.Derived.StreamNameUp
