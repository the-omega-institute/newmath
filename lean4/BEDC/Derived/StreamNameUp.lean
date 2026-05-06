import BEDC.Derived.RatUp
import BEDC.Derived.RatUp.HistoryClassifier

namespace BEDC.Derived.StreamNameUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Cont
open BEDC.FKernel.Bundle
open BEDC.FKernel.Unary
open BEDC.Derived.RatUp

def RatConstStream (d : BHist) : BHist -> BHist :=
  fun _n : BHist => d

def RatStreamNameCarrier (s : BHist -> BHist) : Prop :=
  forall n : BHist, UnaryHistory n -> RatHistoryCarrier (s n)

def RatStreamNameClassifier (s t : BHist -> BHist) : Prop :=
  RatStreamNameCarrier s ∧ RatStreamNameCarrier t ∧
    forall n : BHist, UnaryHistory n -> RatHistoryClassifier (s n) (t n)

def RatStreamNameFiniteWindowClassifier (s t : BHist -> BHist)
    (bundle : ProbeBundle BHist) : Prop :=
  forall n : BHist, InBundle n bundle -> UnaryHistory n -> RatHistoryClassifier (s n) (t n)

def RatStreamName_constant (d : BHist) (_n : BHist) : BHist :=
  append BHist.Empty d

theorem RatStreamNameCarrier_pointwise_hsame_transport {s s' : BHist -> BHist} :
    RatStreamNameCarrier s ->
      (forall n : BHist, UnaryHistory n -> hsame (s n) (s' n)) ->
        RatStreamNameCarrier s' := by
  intro carrier samePoint n nUnary
  exact RatHistoryCarrier_hsame_transport (samePoint n nUnary) (carrier n nUnary)

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

theorem RatStreamNameFiniteWindowClassifier_constant_exactness {h k : BHist}
    {bundle : ProbeBundle BHist} :
    (exists n : BHist, InBundle n bundle ∧ UnaryHistory n) ->
      (RatStreamNameFiniteWindowClassifier (RatConstStream h) (RatConstStream k) bundle ↔
        RatHistoryClassifier h k) := by
  intro bundleWitness
  constructor
  · intro windowClassified
    cases bundleWitness with
    | intro n memberData =>
        exact windowClassified n memberData.left memberData.right
  · intro ratClassified
    intro n _member _nUnary
    cases n with
    | Empty =>
        exact ratClassified
    | e0 _ =>
        exact ratClassified
    | e1 _ =>
        exact ratClassified

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

theorem RatStreamName_independent_reindexed_constant_point_exactness
    {h k : BHist} {r q : BHist -> BHist} :
    (RatStreamNameCarrier (fun n : BHist => RatConstStream h (r n)) ↔
      RatHistoryCarrier h) ∧
      (RatStreamNameClassifier (fun n : BHist => RatConstStream h (r n))
        (fun n : BHist => RatConstStream k (q n)) ↔ RatHistoryClassifier h k) := by
  have carrierH :
      RatStreamNameCarrier (fun n : BHist => RatConstStream h (r n)) ↔
        RatHistoryCarrier h := by
    constructor
    · intro streamCarrier
      have point := streamCarrier BHist.Empty unary_empty
      change RatHistoryCarrier h at point
      exact point
    · intro ratCarrier n _nUnary
      change RatHistoryCarrier h
      exact ratCarrier
  have carrierK :
      RatStreamNameCarrier (fun n : BHist => RatConstStream k (q n)) ↔
        RatHistoryCarrier k := by
    constructor
    · intro streamCarrier
      have point := streamCarrier BHist.Empty unary_empty
      change RatHistoryCarrier k at point
      exact point
    · intro ratCarrier n _nUnary
      change RatHistoryCarrier k
      exact ratCarrier
  have classifierHK :
      RatStreamNameClassifier (fun n : BHist => RatConstStream h (r n))
        (fun n : BHist => RatConstStream k (q n)) ↔ RatHistoryClassifier h k := by
    constructor
    · intro streamClassifier
      have point := streamClassifier.right.right BHist.Empty unary_empty
      change RatHistoryClassifier h k at point
      exact point
    · intro ratClassifier
      exact And.intro (Iff.mpr carrierH ratClassifier.left)
        (And.intro (Iff.mpr carrierK ratClassifier.right.left)
          (fun n _nUnary => by
            change RatHistoryClassifier h k
            exact ratClassifier))
  exact And.intro carrierH classifierHK

theorem RatStreamNameClassifier_observation_e1_pair_readback {s t : BHist -> BHist}
    {n a b : BHist} :
    RatStreamNameClassifier s t -> UnaryHistory n -> hsame (s n) (BHist.e1 a) ->
      hsame (t n) (BHist.e1 b) -> UnaryHistory a ∧ UnaryHistory b ∧ hsame a b := by
  intro classified nUnary sameLeft sameRight
  have pointClassified : RatHistoryClassifier (s n) (t n) :=
    classified.right.right n nUnary
  have displayed : RatHistoryClassifier (BHist.e1 a) (BHist.e1 b) :=
    RatHistoryClassifier_hsame_transport sameLeft sameRight pointClassified
  exact RatHistoryClassifier_e1_tail_unary_iff.mp displayed

theorem RatStreamNameClassifier_unary_context_e1_pair_readback
    {s t : BHist -> BHist}
    {n prefS prefT tailS tailT midS midT outS outT leftTail rightTail : BHist} :
    RatStreamNameClassifier s t -> UnaryHistory n -> UnaryHistory prefS ->
      hsame prefS prefT -> UnaryHistory tailS -> hsame tailS tailT ->
        Cont prefS (s n) midS -> Cont midS tailS outS ->
          Cont prefT (t n) midT -> Cont midT tailT outT ->
            hsame outS (BHist.e1 leftTail) -> hsame outT (BHist.e1 rightTail) ->
              UnaryHistory leftTail ∧ UnaryHistory rightTail ∧ hsame leftTail rightTail := by
  intro classified nUnary prefUnary prefSame tailUnary tailSame prefSCont outSCont
    prefTCont outTCont sameLeft sameRight
  have pointClassified : RatHistoryClassifier (s n) (t n) :=
    classified.right.right n nUnary
  exact RatHistoryClassifier_cont_unary_context_e1_pair_readback pointClassified prefUnary
    prefSame tailUnary tailSame prefSCont outSCont prefTCont outTCont sameLeft sameRight

theorem RatStreamNameClassifier_observation_shape_exclusions {s t : BHist -> BHist}
    {n : BHist} :
    RatStreamNameClassifier s t -> UnaryHistory n ->
      PositiveUnaryDenominator (s n) ∧ PositiveUnaryDenominator (t n) ∧
        UnaryHistory (s n) ∧ UnaryHistory (t n) ∧
          (hsame (s n) BHist.Empty -> False) ∧
            (hsame (t n) BHist.Empty -> False) ∧
              (forall z_s : BHist, hsame (s n) (BHist.e0 z_s) -> False) ∧
                (forall z_t : BHist, hsame (t n) (BHist.e0 z_t) -> False) := by
  intro classified nUnary
  have pointClassified : RatHistoryClassifier (s n) (t n) :=
    classified.right.right n nUnary
  have positives : PositiveUnaryDenominator (s n) ∧ PositiveUnaryDenominator (t n) :=
    RatHistoryClassifier_positive_denominators pointClassified
  have leftRows := PositiveUnaryDenominator_unary_and_nonempty positives.left
  have rightRows := PositiveUnaryDenominator_unary_and_nonempty positives.right
  exact And.intro positives.left
    (And.intro positives.right
      (And.intro leftRows.left
        (And.intro rightRows.left
          (And.intro leftRows.right
            (And.intro rightRows.right
              (And.intro
                (fun z_s sameZero =>
                  PositiveUnaryDenominator_e0_absurd
                    (PositiveUnaryDenominator_hsame_transport sameZero positives.left))
                (fun z_t sameZero =>
                  PositiveUnaryDenominator_e0_absurd
                    (PositiveUnaryDenominator_hsame_transport sameZero positives.right))))))))

theorem RatStreamNameClassifier_transported_observation_shape_exclusions
    {s t s' t' : BHist -> BHist} {n : BHist} :
    RatStreamNameClassifier s t -> UnaryHistory n ->
      (forall k : BHist, UnaryHistory k -> hsame (s k) (s' k)) ->
        (forall k : BHist, UnaryHistory k -> hsame (t k) (t' k)) ->
          PositiveUnaryDenominator (s' n) ∧ PositiveUnaryDenominator (t' n) ∧
            UnaryHistory (s' n) ∧ UnaryHistory (t' n) ∧
              (hsame (s' n) BHist.Empty -> False) ∧
                (hsame (t' n) BHist.Empty -> False) ∧
                  (forall z_s : BHist, hsame (s' n) (BHist.e0 z_s) -> False) ∧
                    (forall z_t : BHist, hsame (t' n) (BHist.e0 z_t) -> False) := by
  intro classified nUnary sameSS' sameTT'
  have pointClassified : RatHistoryClassifier (s' n) (t' n) :=
    RatHistoryClassifier_hsame_transport (sameSS' n nUnary) (sameTT' n nUnary)
      (classified.right.right n nUnary)
  have positives : PositiveUnaryDenominator (s' n) ∧ PositiveUnaryDenominator (t' n) :=
    RatHistoryClassifier_positive_denominators pointClassified
  have leftRows := PositiveUnaryDenominator_unary_and_nonempty positives.left
  have rightRows := PositiveUnaryDenominator_unary_and_nonempty positives.right
  exact And.intro positives.left
    (And.intro positives.right
      (And.intro leftRows.left
        (And.intro rightRows.left
          (And.intro leftRows.right
            (And.intro rightRows.right
              (And.intro
                (fun z_s sameZero =>
                  PositiveUnaryDenominator_e0_absurd
                    (PositiveUnaryDenominator_hsame_transport sameZero positives.left))
                (fun z_t sameZero =>
                  PositiveUnaryDenominator_e0_absurd
                    (PositiveUnaryDenominator_hsame_transport sameZero positives.right))))))))

theorem RatStreamName_independent_reindexed_constant_classifier
    {d e : BHist} {r q : BHist -> BHist} :
    RatHistoryCarrier d ->
      (forall n : BHist, UnaryHistory n -> hsame (RatConstStream d (r n)) d) ∧
        RatStreamNameCarrier (fun n : BHist => RatConstStream d (r n)) ∧
          (RatHistoryClassifier d e ->
            RatStreamNameClassifier (fun n : BHist => RatConstStream d (r n))
              (fun n : BHist => RatConstStream e (q n))) := by
  intro carrierD
  have pointSame :
      forall n : BHist, UnaryHistory n -> hsame (RatConstStream d (r n)) d := by
    intro n _nUnary
    cases r n with
    | Empty => exact hsame_refl d
    | e0 _ => exact hsame_refl d
    | e1 _ => exact hsame_refl d
  have streamCarrier : RatStreamNameCarrier (fun n : BHist => RatConstStream d (r n)) := by
    intro n _nUnary
    cases r n with
    | Empty => exact carrierD
    | e0 _ => exact carrierD
    | e1 _ => exact carrierD
  have classifierLift :
      RatHistoryClassifier d e ->
        RatStreamNameClassifier (fun n : BHist => RatConstStream d (r n))
          (fun n : BHist => RatConstStream e (q n)) := by
    intro ratClassifier
    have carrierE :
        RatStreamNameCarrier (fun n : BHist => RatConstStream e (q n)) := by
      intro n _nUnary
      cases q n with
      | Empty => exact ratClassifier.right.left
      | e0 _ => exact ratClassifier.right.left
      | e1 _ => exact ratClassifier.right.left
    exact And.intro streamCarrier
      (And.intro carrierE
        (fun n _nUnary => by
          cases r n with
          | Empty =>
              cases q n with
              | Empty => exact ratClassifier
              | e0 _ => exact ratClassifier
              | e1 _ => exact ratClassifier
          | e0 _ =>
              cases q n with
              | Empty => exact ratClassifier
              | e0 _ => exact ratClassifier
              | e1 _ => exact ratClassifier
          | e1 _ =>
              cases q n with
              | Empty => exact ratClassifier
              | e0 _ => exact ratClassifier
              | e1 _ => exact ratClassifier))
  exact And.intro pointSame (And.intro streamCarrier classifierLift)

theorem RatStreamNameFiniteWindowClassifier_stability_fields
    {s t u s' t' : BHist -> BHist} {bundle : ProbeBundle BHist} :
    (forall {n : BHist}, InBundle n bundle -> UnaryHistory n -> RatHistoryCarrier (s n)) ->
      RatStreamNameFiniteWindowClassifier s t bundle ->
        RatStreamNameFiniteWindowClassifier t u bundle ->
          (forall {n : BHist}, InBundle n bundle -> UnaryHistory n -> hsame (s n) (s' n)) ->
            (forall {n : BHist}, InBundle n bundle -> UnaryHistory n -> hsame (t n) (t' n)) ->
              RatStreamNameFiniteWindowClassifier s s bundle ∧
                RatStreamNameFiniteWindowClassifier t s bundle ∧
                  RatStreamNameFiniteWindowClassifier s u bundle ∧
                    RatStreamNameFiniteWindowClassifier s' t' bundle := by
  intro carrierS classifiedST classifiedTU sameSS' sameTT'
  have selfS : RatStreamNameFiniteWindowClassifier s s bundle := by
    intro n member nUnary
    exact And.intro (carrierS member nUnary)
      (And.intro (carrierS member nUnary) (hsame_refl (s n)))
  have symmTS : RatStreamNameFiniteWindowClassifier t s bundle := by
    intro n member nUnary
    exact RatHistoryClassifier_symm (classifiedST n member nUnary)
  have transSU : RatStreamNameFiniteWindowClassifier s u bundle := by
    intro n member nUnary
    exact RatHistoryClassifier_trans (classifiedST n member nUnary)
      (classifiedTU n member nUnary)
  have transportS'T' : RatStreamNameFiniteWindowClassifier s' t' bundle := by
    intro n member nUnary
    exact RatHistoryClassifier_hsame_transport (sameSS' member nUnary)
      (sameTT' member nUnary) (classifiedST n member nUnary)
  exact And.intro selfS (And.intro symmTS (And.intro transSU transportS'T'))

end BEDC.Derived.StreamNameUp
