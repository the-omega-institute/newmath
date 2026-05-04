import BEDC.Derived.RatUp
import BEDC.Derived.RatUp.HistoryClassifier
import BEDC.Derived.StreamNameUp

namespace BEDC.Derived.RealUp

open BEDC.FKernel.Hist
open BEDC.Derived.RatUp
open BEDC.Derived.StreamNameUp
open BEDC.FKernel.Unary

def RealConstantHistoryCarrier (h : BHist) : Prop :=
  ∃ d : BHist, hsame h (BHist.e1 d) ∧ RatHistoryCarrier d

def RealConstantHistoryClassifier (h k : BHist) : Prop :=
  ∃ d : BHist, ∃ e : BHist,
    hsame h (BHist.e1 d) ∧ hsame k (BHist.e1 e) ∧ RatHistoryClassifier d e

theorem RealConstantHistoryCarrier_e1_iff_rat {d : BHist} :
    RealConstantHistoryCarrier (BHist.e1 d) ↔ RatHistoryCarrier d := by
  constructor
  · intro carrier
    cases carrier with
    | intro witness data =>
        cases data with
        | intro same witnessCarrier =>
            exact RatHistoryCarrier_hsame_transport
              (hsame_symm (hsame_e1_iff.mp same)) witnessCarrier
  · intro ratCarrier
    exact ⟨d, hsame_refl (BHist.e1 d), ratCarrier⟩

theorem RealConstantHistoryCarrier_e0_absurd {tail : BHist} :
    RealConstantHistoryCarrier (BHist.e0 tail) → False := by
  intro carrier
  cases carrier with
  | intro witness data =>
      exact not_hsame_e0_e1 data.left

theorem RealConstantHistoryCarrier_empty_absurd :
    RealConstantHistoryCarrier BHist.Empty -> False := by
  intro carrier
  cases carrier with
  | intro witness data =>
      exact not_hsame_emp_e1 data.left

theorem RealConstantHistoryClassifier_e1_iff_rat {d e : BHist} :
    RealConstantHistoryClassifier (BHist.e1 d) (BHist.e1 e) ↔
      RatHistoryClassifier d e := by
  constructor
  · intro classifier
    cases classifier with
    | intro dWitness rest =>
        cases rest with
        | intro eWitness data =>
            cases data with
            | intro sameD rest =>
                cases rest with
                | intro sameE ratClassifier =>
                    exact RatHistoryClassifier_hsame_transport
                      (hsame_symm (hsame_e1_iff.mp sameD))
                      (hsame_symm (hsame_e1_iff.mp sameE))
                      ratClassifier
  · intro ratClassifier
    exact ⟨d, e, hsame_refl (BHist.e1 d), hsame_refl (BHist.e1 e), ratClassifier⟩

theorem RealConstantHistoryClassifier_endpoint_transport {h h' k k' : BHist} :
    hsame h h' -> hsame k k' -> RealConstantHistoryClassifier h k ->
      RealConstantHistoryClassifier h' k' := by
  intro sameH sameK classified
  cases classified with
  | intro d rest =>
      cases rest with
      | intro e data =>
          cases data with
          | intro sameHD rest =>
              cases rest with
              | intro sameKE ratClassifier =>
                  exact ⟨d, e, hsame_trans (hsame_symm sameH) sameHD,
                    hsame_trans (hsame_symm sameK) sameKE, ratClassifier⟩

theorem RealConstantHistoryClassifier_endpoint_carriers {h k : BHist} :
    RealConstantHistoryClassifier h k → RealConstantHistoryCarrier h ∧
      RealConstantHistoryCarrier k := by
  intro classifier
  cases classifier with
  | intro d rest =>
      cases rest with
      | intro e data =>
          cases data with
          | intro sameH rest =>
              cases rest with
              | intro sameK ratClassifier =>
                  constructor
                  · exact ⟨d, sameH, ratClassifier.left⟩
                  · exact ⟨e, sameK, ratClassifier.right.left⟩

def RealStreamClassifier (x y : Nat -> BHist) : Prop :=
  forall n : Nat, BEDC.Derived.RatUp.RatHistoryClassifier (x n) (y n)

def RealStreamPrefixClassifier (x y : Nat -> BHist) : Nat -> Prop :=
  Nat.rec
    (BEDC.Derived.RatUp.RatHistoryClassifier (x Nat.zero) (y Nat.zero))
    (fun n acc => And acc
      (BEDC.Derived.RatUp.RatHistoryClassifier (x (Nat.succ n)) (y (Nat.succ n))))

def RealUnaryStreamClassifier (s t : BHist -> BHist) : Prop :=
  forall n : BHist, UnaryHistory n -> RatHistoryClassifier (s n) (t n)

theorem RealStreamClassifier_prefix {x y : Nat -> BHist} :
    RealStreamClassifier x y -> forall n : Nat, RealStreamPrefixClassifier x y n := by
  intro classified n
  induction n with
  | zero =>
      exact classified Nat.zero
  | succ n ih =>
      exact And.intro ih (classified (Nat.succ n))

theorem RealStreamPrefixClassifier_endpoint {x y : Nat -> BHist} :
    forall n : Nat, RealStreamPrefixClassifier x y n -> RatHistoryClassifier (x n) (y n) := by
  intro n
  cases n with
  | zero =>
      intro classified
      exact classified
  | succ n =>
      intro classified
      exact classified.right

theorem RealStreamPrefixClassifier_base_of_successor {x y : Nat -> BHist} :
    forall n : Nat, RealStreamPrefixClassifier x y (Nat.succ n) ->
      RealStreamPrefixClassifier x y Nat.zero := by
  intro n
  induction n with
  | zero =>
      intro classified
      exact classified.left
  | succ _ ih =>
      intro classified
      exact ih classified.left

theorem RealStreamClassifier_finite_prefix_exactness {x y : Nat -> BHist} :
    RealStreamClassifier x y <-> forall n : Nat, RealStreamPrefixClassifier x y n := by
  constructor
  · intro classified n
    exact RealStreamClassifier_prefix classified n
  · intro prefixes n
    exact RealStreamPrefixClassifier_endpoint n (prefixes n)

theorem RealStreamClassifier_symm {x y : Nat -> BHist} :
    RealStreamClassifier x y -> RealStreamClassifier y x := by
  intro classified n
  exact RatHistoryClassifier_symm (classified n)

theorem RealStreamClassifier_trans {x y z : Nat -> BHist} :
    RealStreamClassifier x y -> RealStreamClassifier y z -> RealStreamClassifier x z := by
  intro classifiedXY classifiedYZ n
  exact RatHistoryClassifier_trans (classifiedXY n) (classifiedYZ n)

theorem RealStreamPrefixClassifier_hsame_transport {x x' y y' : Nat -> BHist}
    (sameX : forall n : Nat, hsame (x n) (x' n))
    (sameY : forall n : Nat, hsame (y n) (y' n)) :
    forall n : Nat, RealStreamPrefixClassifier x y n ->
      RealStreamPrefixClassifier x' y' n := by
  intro n
  induction n with
  | zero =>
      intro classified
      exact BEDC.Derived.RatUp.RatHistoryClassifier_hsame_transport
        (sameX Nat.zero) (sameY Nat.zero) classified
  | succ n ih =>
      intro classified
      exact And.intro (ih classified.left)
        (BEDC.Derived.RatUp.RatHistoryClassifier_hsame_transport
          (sameX (Nat.succ n)) (sameY (Nat.succ n)) classified.right)

theorem RealStreamPrefixClassifier_symm {x y : Nat -> BHist} :
    forall n : Nat, RealStreamPrefixClassifier x y n ->
      RealStreamPrefixClassifier y x n := by
  intro n
  induction n with
  | zero =>
      intro classified
      exact RatHistoryClassifier_symm classified
  | succ n ih =>
      intro classified
      exact And.intro (ih classified.left) (RatHistoryClassifier_symm classified.right)

theorem RealStreamPrefixClassifier_trans {x y z : Nat -> BHist} :
    forall n : Nat, RealStreamPrefixClassifier x y n -> RealStreamPrefixClassifier y z n ->
      RealStreamPrefixClassifier x z n := by
  intro n
  induction n with
  | zero =>
      intro classifiedXY classifiedYZ
      exact RatHistoryClassifier_trans classifiedXY classifiedYZ
  | succ n ih =>
      intro classifiedXY classifiedYZ
      exact And.intro
        (ih classifiedXY.left classifiedYZ.left)
        (RatHistoryClassifier_trans classifiedXY.right classifiedYZ.right)

theorem RealStreamPrefixClassifier_refl {x : Nat -> BHist}
    (carrier : forall n : Nat, RatHistoryCarrier (x n)) :
    forall n : Nat, RealStreamPrefixClassifier x x n := by
  intro n
  induction n with
  | zero =>
      exact And.intro (carrier Nat.zero)
        (And.intro (carrier Nat.zero) (hsame_refl (x Nat.zero)))
  | succ n ih =>
      exact And.intro ih
        (And.intro (carrier (Nat.succ n))
          (And.intro (carrier (Nat.succ n)) (hsame_refl (x (Nat.succ n)))))

theorem RealStreamPrefixClassifier_e1_pair_readback {x y : Nat -> BHist} :
    forall {n : Nat} {leftTail rightTail : BHist},
      RealStreamPrefixClassifier x y n ->
        hsame (x n) (BHist.e1 leftTail) ->
          hsame (y n) (BHist.e1 rightTail) ->
            And (UnaryHistory leftTail) (And (UnaryHistory rightTail) (hsame leftTail rightTail)) := by
  intro n
  cases n with
  | zero =>
      intro leftTail rightTail classified sameLeft sameRight
      have displayed :=
        BEDC.Derived.RatUp.RatHistoryClassifier_hsame_transport sameLeft sameRight classified
      exact BEDC.Derived.RatUp.RatHistoryClassifier_e1_tail_unary_iff.mp displayed
  | succ n =>
      intro leftTail rightTail classified sameLeft sameRight
      have displayed :=
        BEDC.Derived.RatUp.RatHistoryClassifier_hsame_transport sameLeft sameRight
          classified.right
      exact BEDC.Derived.RatUp.RatHistoryClassifier_e1_tail_unary_iff.mp displayed

theorem RealStreamPrefixClassifier_previous_with_unary {x y : Nat -> BHist} :
    (forall i : Nat, UnaryHistory (x i)) -> forall n : Nat,
      RealStreamPrefixClassifier x y (Nat.succ n) ->
        RealStreamPrefixClassifier x y n ∧ UnaryHistory (x n) := by
  intro unary n classified
  exact And.intro classified.left (unary n)

theorem RealStreamPrefixClassifier_add_left_previous_with_unary {x y : Nat -> BHist} :
    (forall i : Nat, UnaryHistory (x i)) -> forall n m : Nat,
      RealStreamPrefixClassifier x y (m + n) ->
        RealStreamPrefixClassifier x y n ∧ UnaryHistory (x n) := by
  intro unary n m
  induction m with
  | zero =>
      intro classified
      simp only [Nat.zero_add] at classified
      exact And.intro classified (unary n)
  | succ m ih =>
      intro classified
      have stepClassified : RealStreamPrefixClassifier x y (Nat.succ (m + n)) := by
        simp only [Nat.succ_add] at classified
        exact classified
      have peeled := RealStreamPrefixClassifier_previous_with_unary unary (m + n) stepClassified
      exact ih peeled.left

theorem RealConstantStreamCarrier_streamName_bridge {d : BHist} :
    hsame (RatConstStream d BHist.Empty) d ∧
      ((RatHistoryCarrier d ↔ RatStreamNameCarrier (RatConstStream d)) ∧
        (RatStreamNameCarrier (RatConstStream d) ↔
          RealConstantHistoryCarrier (BHist.e1 d))) := by
  have exactness :=
    RatStreamName_constant_point_exactness (h := d) (k := d)
  have streamCarrierIff : RatStreamNameCarrier (RatConstStream d) ↔ RatHistoryCarrier d :=
    exactness.right.right.left
  have ratStreamIff : RatHistoryCarrier d ↔ RatStreamNameCarrier (RatConstStream d) := by
    constructor
    · intro ratCarrier
      exact Iff.mpr streamCarrierIff ratCarrier
    · intro streamCarrier
      exact Iff.mp streamCarrierIff streamCarrier
  have streamRealIff :
      RatStreamNameCarrier (RatConstStream d) ↔
        RealConstantHistoryCarrier (BHist.e1 d) := by
    constructor
    · intro streamCarrier
      exact Iff.mpr RealConstantHistoryCarrier_e1_iff_rat
        (Iff.mp streamCarrierIff streamCarrier)
    · intro realCarrier
      exact Iff.mpr streamCarrierIff
        (Iff.mp RealConstantHistoryCarrier_e1_iff_rat realCarrier)
  exact And.intro exactness.left (And.intro ratStreamIff streamRealIff)

theorem RealConstantStream_streamName_bridge {d e : BHist} :
    (RatHistoryClassifier d e ↔
      RatStreamNameClassifier (RatConstStream d) (RatConstStream e)) ∧
      (RatStreamNameClassifier (RatConstStream d) (RatConstStream e) ↔
        RealUnaryStreamClassifier (RatConstStream d) (RatConstStream e)) ∧
        (RealUnaryStreamClassifier (RatConstStream d) (RatConstStream e) ↔
          RealConstantHistoryClassifier (BHist.e1 d) (BHist.e1 e)) := by
  have exactnessDE :=
    RatStreamName_constant_point_exactness (h := d) (k := e)
  have exactnessED :=
    RatStreamName_constant_point_exactness (h := e) (k := d)
  have carrierD :
      RatStreamNameCarrier (RatConstStream d) ↔ RatHistoryCarrier d :=
    exactnessDE.right.right.left
  have carrierE :
      RatStreamNameCarrier (RatConstStream e) ↔ RatHistoryCarrier e :=
    exactnessED.right.right.left
  have streamClassifierIff :
      RatStreamNameClassifier (RatConstStream d) (RatConstStream e) ↔
        RatHistoryClassifier d e :=
    exactnessDE.right.right.right
  have ratStreamIff :
      RatHistoryClassifier d e ↔
        RatStreamNameClassifier (RatConstStream d) (RatConstStream e) := by
    constructor
    · intro ratClassifier
      exact Iff.mpr streamClassifierIff ratClassifier
    · intro streamClassifier
      exact Iff.mp streamClassifierIff streamClassifier
  have streamUnaryIff :
      RatStreamNameClassifier (RatConstStream d) (RatConstStream e) ↔
        RealUnaryStreamClassifier (RatConstStream d) (RatConstStream e) := by
    constructor
    · intro streamClassifier
      exact streamClassifier.right.right
    · intro unaryClassifier
      have ratClassifier : RatHistoryClassifier d e :=
        unaryClassifier BHist.Empty unary_empty
      exact And.intro (Iff.mpr carrierD ratClassifier.left)
        (And.intro (Iff.mpr carrierE ratClassifier.right.left) unaryClassifier)
  have unaryRealIff :
      RealUnaryStreamClassifier (RatConstStream d) (RatConstStream e) ↔
        RealConstantHistoryClassifier (BHist.e1 d) (BHist.e1 e) := by
    constructor
    · intro unaryClassifier
      exact Iff.mpr RealConstantHistoryClassifier_e1_iff_rat
        (unaryClassifier BHist.Empty unary_empty)
    · intro realClassifier n _nUnary
      have ratClassifier : RatHistoryClassifier d e :=
        Iff.mp RealConstantHistoryClassifier_e1_iff_rat realClassifier
      cases n with
      | Empty => exact ratClassifier
      | e0 _ => exact ratClassifier
      | e1 _ => exact ratClassifier
  exact And.intro ratStreamIff (And.intro streamUnaryIff unaryRealIff)

theorem RealConstantStreamCarrier_reindexed_streamName_bridge {d : BHist}
    {r : BHist -> BHist} :
    (RatHistoryCarrier d ↔
      RatStreamNameCarrier (fun n : BHist => RatConstStream d (r n))) ∧
      (RatStreamNameCarrier (fun n : BHist => RatConstStream d (r n)) ↔
        RealConstantHistoryCarrier (BHist.e1 d)) := by
  have streamCarrierIff :
      RatStreamNameCarrier (fun n : BHist => RatConstStream d (r n)) ↔
        RatHistoryCarrier d := by
    constructor
    · intro streamCarrier
      have atEmpty := streamCarrier BHist.Empty unary_empty
      cases h : r BHist.Empty with
      | Empty =>
          simp only [h, RatConstStream] at atEmpty
          exact atEmpty
      | e0 _ =>
          simp only [h, RatConstStream] at atEmpty
          exact atEmpty
      | e1 _ =>
          simp only [h, RatConstStream] at atEmpty
          exact atEmpty
    · intro ratCarrier n _nUnary
      cases h : r n with
      | Empty =>
          simp only [h, RatConstStream]
          exact ratCarrier
      | e0 _ =>
          simp only [h, RatConstStream]
          exact ratCarrier
      | e1 _ =>
          simp only [h, RatConstStream]
          exact ratCarrier
  have ratStreamIff :
      RatHistoryCarrier d ↔
        RatStreamNameCarrier (fun n : BHist => RatConstStream d (r n)) := by
    constructor
    · intro ratCarrier
      exact Iff.mpr streamCarrierIff ratCarrier
    · intro streamCarrier
      exact Iff.mp streamCarrierIff streamCarrier
  have streamRealIff :
      RatStreamNameCarrier (fun n : BHist => RatConstStream d (r n)) ↔
        RealConstantHistoryCarrier (BHist.e1 d) := by
    constructor
    · intro streamCarrier
      exact Iff.mpr RealConstantHistoryCarrier_e1_iff_rat
        (Iff.mp streamCarrierIff streamCarrier)
    · intro realCarrier
      exact Iff.mpr streamCarrierIff
        (Iff.mp RealConstantHistoryCarrier_e1_iff_rat realCarrier)
  exact And.intro ratStreamIff streamRealIff

theorem RealConstantStream_reindexed_streamName_bridge {d e : BHist}
    {r : BHist -> BHist} :
    (RatHistoryClassifier d e ↔
      RatStreamNameClassifier
        (fun n : BHist => RatConstStream d (r n))
        (fun n : BHist => RatConstStream e (r n))) ∧
      (RatStreamNameClassifier
        (fun n : BHist => RatConstStream d (r n))
        (fun n : BHist => RatConstStream e (r n)) ↔
          RealUnaryStreamClassifier
            (fun n : BHist => RatConstStream d (r n))
            (fun n : BHist => RatConstStream e (r n))) ∧
        (RealUnaryStreamClassifier
          (fun n : BHist => RatConstStream d (r n))
          (fun n : BHist => RatConstStream e (r n)) ↔
            RealConstantHistoryClassifier (BHist.e1 d) (BHist.e1 e)) := by
  have carrierD :
      RatStreamNameCarrier (fun n : BHist => RatConstStream d (r n)) ↔
        RatHistoryCarrier d :=
    (RealConstantStreamCarrier_reindexed_streamName_bridge (d := d) (r := r)).left.symm
  have carrierE :
      RatStreamNameCarrier (fun n : BHist => RatConstStream e (r n)) ↔
        RatHistoryCarrier e :=
    (RealConstantStreamCarrier_reindexed_streamName_bridge (d := e) (r := r)).left.symm
  have streamClassifierIff :
      RatStreamNameClassifier
        (fun n : BHist => RatConstStream d (r n))
        (fun n : BHist => RatConstStream e (r n)) ↔
          RatHistoryClassifier d e := by
    constructor
    · intro streamClassifier
      have atEmpty := streamClassifier.right.right BHist.Empty unary_empty
      cases h : r BHist.Empty with
      | Empty =>
          simp only [h, RatConstStream] at atEmpty
          exact atEmpty
      | e0 _ =>
          simp only [h, RatConstStream] at atEmpty
          exact atEmpty
      | e1 _ =>
          simp only [h, RatConstStream] at atEmpty
          exact atEmpty
    · intro ratClassifier
      exact And.intro (Iff.mpr carrierD ratClassifier.left)
        (And.intro (Iff.mpr carrierE ratClassifier.right.left)
          (fun n _nUnary => by
            cases h : r n with
            | Empty =>
                simp only [h, RatConstStream]
                exact ratClassifier
            | e0 _ =>
                simp only [h, RatConstStream]
                exact ratClassifier
            | e1 _ =>
                simp only [h, RatConstStream]
                exact ratClassifier))
  have ratStreamIff :
      RatHistoryClassifier d e ↔
        RatStreamNameClassifier
          (fun n : BHist => RatConstStream d (r n))
          (fun n : BHist => RatConstStream e (r n)) := by
    constructor
    · intro ratClassifier
      exact Iff.mpr streamClassifierIff ratClassifier
    · intro streamClassifier
      exact Iff.mp streamClassifierIff streamClassifier
  have streamUnaryIff :
      RatStreamNameClassifier
        (fun n : BHist => RatConstStream d (r n))
        (fun n : BHist => RatConstStream e (r n)) ↔
          RealUnaryStreamClassifier
            (fun n : BHist => RatConstStream d (r n))
            (fun n : BHist => RatConstStream e (r n)) := by
    constructor
    · intro streamClassifier
      exact streamClassifier.right.right
    · intro unaryClassifier
      have ratClassifier : RatHistoryClassifier d e := by
        have atEmpty := unaryClassifier BHist.Empty unary_empty
        cases h : r BHist.Empty with
        | Empty =>
            simp only [h, RatConstStream] at atEmpty
            exact atEmpty
        | e0 _ =>
            simp only [h, RatConstStream] at atEmpty
            exact atEmpty
        | e1 _ =>
            simp only [h, RatConstStream] at atEmpty
            exact atEmpty
      exact And.intro (Iff.mpr carrierD ratClassifier.left)
        (And.intro (Iff.mpr carrierE ratClassifier.right.left) unaryClassifier)
  have unaryRealIff :
      RealUnaryStreamClassifier
        (fun n : BHist => RatConstStream d (r n))
        (fun n : BHist => RatConstStream e (r n)) ↔
          RealConstantHistoryClassifier (BHist.e1 d) (BHist.e1 e) := by
    constructor
    · intro unaryClassifier
      have ratClassifier : RatHistoryClassifier d e := by
        have atEmpty := unaryClassifier BHist.Empty unary_empty
        cases h : r BHist.Empty with
        | Empty =>
            simp only [h, RatConstStream] at atEmpty
            exact atEmpty
        | e0 _ =>
            simp only [h, RatConstStream] at atEmpty
            exact atEmpty
        | e1 _ =>
            simp only [h, RatConstStream] at atEmpty
            exact atEmpty
      exact Iff.mpr RealConstantHistoryClassifier_e1_iff_rat ratClassifier
    · intro realClassifier n _nUnary
      have ratClassifier : RatHistoryClassifier d e :=
        Iff.mp RealConstantHistoryClassifier_e1_iff_rat realClassifier
      cases h : r n with
      | Empty =>
          simp only [h, RatConstStream]
          exact ratClassifier
      | e0 _ =>
          simp only [h, RatConstStream]
          exact ratClassifier
      | e1 _ =>
          simp only [h, RatConstStream]
          exact ratClassifier
  exact And.intro ratStreamIff (And.intro streamUnaryIff unaryRealIff)

theorem RealConstantHistoryClassifier_equivalence_fields :
    (∀ {h : BHist}, RealConstantHistoryCarrier h → RealConstantHistoryClassifier h h) ∧
      (∀ {h k : BHist}, RealConstantHistoryClassifier h k → RealConstantHistoryClassifier k h) ∧
        (∀ {h k l : BHist}, RealConstantHistoryClassifier h k →
          RealConstantHistoryClassifier k l → RealConstantHistoryClassifier h l) := by
  constructor
  · intro h carrier
    cases carrier with
    | intro d data =>
        cases data with
        | intro sameHD ratCarrier =>
            exact ⟨d, d, sameHD, sameHD,
              And.intro ratCarrier (And.intro ratCarrier (hsame_refl d))⟩
  · constructor
    · intro h k classifier
      cases classifier with
      | intro d rest =>
          cases rest with
          | intro e data =>
              cases data with
              | intro sameHD rest =>
                  cases rest with
                  | intro sameKE ratClassifier =>
                      exact ⟨e, d, sameKE, sameHD, RatHistoryClassifier_symm ratClassifier⟩
    · intro h k l classifierHK classifierKL
      cases classifierHK with
      | intro d hkRest =>
          cases hkRest with
          | intro e hkData =>
              cases hkData with
              | intro sameHD hkRest =>
                  cases hkRest with
                  | intro sameKE ratDE =>
                      cases classifierKL with
                      | intro e' klRest =>
                          cases klRest with
                          | intro f klData =>
                              cases klData with
                              | intro sameKE' klRest =>
                                  cases klRest with
                                  | intro sameLF ratE'F =>
                                      have sameEE' : hsame e e' :=
                                        hsame_e1_iff.mp
                                          (hsame_trans (hsame_symm sameKE) sameKE')
                                      have ratEF : RatHistoryClassifier e f :=
                                        RatHistoryClassifier_hsame_transport
                                          (hsame_symm sameEE') (hsame_refl f) ratE'F
                                      exact ⟨d, f, sameHD, sameLF,
                                        RatHistoryClassifier_trans ratDE ratEF⟩

end BEDC.Derived.RealUp
