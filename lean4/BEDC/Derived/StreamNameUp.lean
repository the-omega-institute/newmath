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

theorem RatConstStream_empty_point_exactness {h k : BHist} :
    (RatStreamNameCarrier (RatConstStream h) ↔
      RatHistoryCarrier (RatConstStream h BHist.Empty)) ∧
      (RatStreamNameClassifier (RatConstStream h) (RatConstStream k) ↔
        RatHistoryClassifier (RatConstStream h BHist.Empty) (RatConstStream k BHist.Empty)) := by
  constructor
  · constructor
    · intro carrier
      exact carrier BHist.Empty unary_empty
    · intro pointCarrier
      intro n _nUnary
      cases n with
      | Empty =>
          exact pointCarrier
      | e0 tail =>
          exact pointCarrier
      | e1 tail =>
          exact pointCarrier
  · constructor
    · intro classified
      exact classified.right.right BHist.Empty unary_empty
    · intro pointClassified
      have carrierH : RatStreamNameCarrier (RatConstStream h) := by
        intro n _nUnary
        cases n with
        | Empty =>
            exact pointClassified.left
        | e0 tail =>
            exact pointClassified.left
        | e1 tail =>
            exact pointClassified.left
      have carrierK : RatStreamNameCarrier (RatConstStream k) := by
        intro n _nUnary
        cases n with
        | Empty =>
            exact pointClassified.right.left
        | e0 tail =>
            exact pointClassified.right.left
        | e1 tail =>
            exact pointClassified.right.left
      exact And.intro carrierH
        (And.intro carrierK
          (fun n _nUnary =>
            match n with
            | BHist.Empty => pointClassified
            | BHist.e0 _ => pointClassified
            | BHist.e1 _ => pointClassified))

theorem RatStreamName_reindexing_and_map_stability {s t r F : BHist -> BHist}
    (rUnary : forall n : BHist, UnaryHistory n -> UnaryHistory (r n))
    (mapCarrier : forall h : BHist, RatHistoryCarrier h -> RatHistoryCarrier (F h))
    (mapClassifier : forall h k : BHist, RatHistoryClassifier h k ->
      RatHistoryClassifier (F h) (F k)) :
    (RatStreamNameCarrier s -> RatStreamNameCarrier (fun n => s (r n))) ∧
      (RatStreamNameClassifier s t ->
        RatStreamNameClassifier (fun n => s (r n)) (fun n => t (r n))) ∧
        (RatStreamNameCarrier s -> RatStreamNameCarrier (fun n => F (s n))) ∧
          (RatStreamNameClassifier s t ->
            RatStreamNameClassifier (fun n => F (s n)) (fun n => F (t n))) := by
  constructor
  · intro carrierS n nUnary
    exact carrierS (r n) (rUnary n nUnary)
  · constructor
    · intro classified
      exact And.intro
        (fun n nUnary => classified.left (r n) (rUnary n nUnary))
        (And.intro
          (fun n nUnary => classified.right.left (r n) (rUnary n nUnary))
          (fun n nUnary => classified.right.right (r n) (rUnary n nUnary)))
    · constructor
      · intro carrierS n nUnary
        exact mapCarrier (s n) (carrierS n nUnary)
      · intro classified
        exact And.intro
          (fun n nUnary => mapCarrier (s n) (classified.left n nUnary))
          (And.intro
            (fun n nUnary => mapCarrier (t n) (classified.right.left n nUnary))
            (fun n nUnary => mapClassifier (s n) (t n)
              (classified.right.right n nUnary)))

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

theorem RatStreamName_reindexing_composition_law {s t : BHist -> BHist}
    {r q : BHist -> BHist}
    (r_unary : forall n : BHist, UnaryHistory n -> UnaryHistory (r n))
    (q_unary : forall n : BHist, UnaryHistory n -> UnaryHistory (q n)) :
    (forall n : BHist, UnaryHistory n -> UnaryHistory (q (r n))) ∧
      (RatStreamNameCarrier s -> RatStreamNameCarrier (fun n => s (q (r n)))) ∧
        (RatStreamNameClassifier s t ->
          RatStreamNameClassifier (fun n => s (q (r n))) (fun n => t (q (r n)))) := by
  have compositeUnary : forall n : BHist, UnaryHistory n -> UnaryHistory (q (r n)) := by
    intro n nUnary
    exact q_unary (r n) (r_unary n nUnary)
  constructor
  · exact compositeUnary
  · constructor
    · intro carrierS n nUnary
      exact carrierS (q (r n)) (compositeUnary n nUnary)
    · intro classified
      constructor
      · intro n nUnary
        exact classified.left (q (r n)) (compositeUnary n nUnary)
      · constructor
        · intro n nUnary
          exact classified.right.left (q (r n)) (compositeUnary n nUnary)
        · intro n nUnary
          exact classified.right.right (q (r n)) (compositeUnary n nUnary)

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
