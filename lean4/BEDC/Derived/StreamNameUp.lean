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

theorem RatStreamName_constant_witness {d e : BHist} :
    (forall n : BHist, UnaryHistory n -> hsame (RatConstStream d n) d) ∧
      (RatHistoryCarrier d -> RatStreamNameCarrier (RatConstStream d) ∧
        RatStreamNameClassifier (RatConstStream d) (RatConstStream d)) ∧
        (RatHistoryClassifier d e ->
          RatStreamNameClassifier (RatConstStream d) (RatConstStream e)) := by
  have pointSame : forall n : BHist, UnaryHistory n -> hsame (RatConstStream d n) d := by
    intro n _nUnary
    cases n with
    | Empty => exact hsame_refl d
    | e0 _ => exact hsame_refl d
    | e1 _ => exact hsame_refl d
  have carrierSelf :
      RatHistoryCarrier d -> RatStreamNameCarrier (RatConstStream d) ∧
        RatStreamNameClassifier (RatConstStream d) (RatConstStream d) := by
    intro carrierD
    have streamCarrier : RatStreamNameCarrier (RatConstStream d) := by
      intro n _nUnary
      cases n with
      | Empty => exact carrierD
      | e0 _ => exact carrierD
      | e1 _ => exact carrierD
    have selfClassifier : RatStreamNameClassifier (RatConstStream d) (RatConstStream d) := by
      exact And.intro streamCarrier
        (And.intro streamCarrier
          (fun n _nUnary => by
            cases n with
            | Empty => exact And.intro carrierD (And.intro carrierD (hsame_refl d))
            | e0 _ => exact And.intro carrierD (And.intro carrierD (hsame_refl d))
            | e1 _ => exact And.intro carrierD (And.intro carrierD (hsame_refl d))))
    exact And.intro streamCarrier selfClassifier
  have classifierLift :
      RatHistoryClassifier d e ->
        RatStreamNameClassifier (RatConstStream d) (RatConstStream e) := by
    intro ratClassifier
    have carrierD : RatStreamNameCarrier (RatConstStream d) := by
      intro n _nUnary
      cases n with
      | Empty => exact ratClassifier.left
      | e0 _ => exact ratClassifier.left
      | e1 _ => exact ratClassifier.left
    have carrierE : RatStreamNameCarrier (RatConstStream e) := by
      intro n _nUnary
      cases n with
      | Empty => exact ratClassifier.right.left
      | e0 _ => exact ratClassifier.right.left
      | e1 _ => exact ratClassifier.right.left
    exact And.intro carrierD
      (And.intro carrierE
        (fun n _nUnary => by
          cases n with
          | Empty => exact ratClassifier
          | e0 _ => exact ratClassifier
          | e1 _ => exact ratClassifier))
  exact And.intro pointSame (And.intro carrierSelf classifierLift)

theorem RatStreamName_constant_reindexing_classifier {d e : BHist} {r : BHist -> BHist}
    (preservesUnary : forall n : BHist, UnaryHistory n -> UnaryHistory (r n)) :
    RatHistoryCarrier d -> RatStreamNameCarrier (fun n => RatConstStream d (r n)) ∧
      RatStreamNameClassifier (fun n => RatConstStream d (r n)) (RatConstStream d) ∧
        (RatHistoryClassifier d e ->
          RatStreamNameClassifier (fun n => RatConstStream d (r n))
            (fun n => RatConstStream e (r n))) := by
  intro carrierD
  have reindexedCarrier : RatStreamNameCarrier (fun n => RatConstStream d (r n)) := by
    intro n nUnary
    have _rnUnary : UnaryHistory (r n) := preservesUnary n nUnary
    change RatHistoryCarrier (RatConstStream d (r n))
    cases h : r n with
    | Empty => exact carrierD
    | e0 _ => exact carrierD
    | e1 _ => exact carrierD
  have constantCarrier : RatStreamNameCarrier (RatConstStream d) := by
    intro n _nUnary
    cases n with
    | Empty => exact carrierD
    | e0 _ => exact carrierD
    | e1 _ => exact carrierD
  have selfClassifier :
      RatStreamNameClassifier (fun n => RatConstStream d (r n)) (RatConstStream d) := by
    exact And.intro reindexedCarrier
      (And.intro constantCarrier
        (fun n nUnary => by
          have _rnUnary : UnaryHistory (r n) := preservesUnary n nUnary
          change RatHistoryClassifier (RatConstStream d (r n)) (RatConstStream d n)
          cases h : r n with
          | Empty =>
              cases n with
              | Empty => exact And.intro carrierD (And.intro carrierD (hsame_refl d))
              | e0 _ => exact And.intro carrierD (And.intro carrierD (hsame_refl d))
              | e1 _ => exact And.intro carrierD (And.intro carrierD (hsame_refl d))
          | e0 _ =>
              cases n with
              | Empty => exact And.intro carrierD (And.intro carrierD (hsame_refl d))
              | e0 _ => exact And.intro carrierD (And.intro carrierD (hsame_refl d))
              | e1 _ => exact And.intro carrierD (And.intro carrierD (hsame_refl d))
          | e1 _ =>
              cases n with
              | Empty => exact And.intro carrierD (And.intro carrierD (hsame_refl d))
              | e0 _ => exact And.intro carrierD (And.intro carrierD (hsame_refl d))
              | e1 _ => exact And.intro carrierD (And.intro carrierD (hsame_refl d))))
  have classifierLift :
      RatHistoryClassifier d e ->
        RatStreamNameClassifier (fun n => RatConstStream d (r n))
          (fun n => RatConstStream e (r n)) := by
    intro ratClassifier
    have carrierE : RatStreamNameCarrier (fun n => RatConstStream e (r n)) := by
      intro n nUnary
      have _rnUnary : UnaryHistory (r n) := preservesUnary n nUnary
      change RatHistoryCarrier (RatConstStream e (r n))
      cases h : r n with
      | Empty => exact ratClassifier.right.left
      | e0 _ => exact ratClassifier.right.left
      | e1 _ => exact ratClassifier.right.left
    exact And.intro reindexedCarrier
      (And.intro carrierE
        (fun n nUnary => by
          have _rnUnary : UnaryHistory (r n) := preservesUnary n nUnary
          change RatHistoryClassifier (RatConstStream d (r n)) (RatConstStream e (r n))
          cases h : r n with
          | Empty => exact ratClassifier
          | e0 _ => exact ratClassifier
          | e1 _ => exact ratClassifier))
  exact And.intro reindexedCarrier (And.intro selfClassifier classifierLift)

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
