import BEDC.Derived.RealUp

namespace BEDC.Derived.RealUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Unary
open BEDC.Derived.RatUp
open BEDC.Derived.StreamNameUp

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
          simp only [RatConstStream] at atEmpty
          exact atEmpty
      | e0 _ =>
          simp only [RatConstStream] at atEmpty
          exact atEmpty
      | e1 _ =>
          simp only [RatConstStream] at atEmpty
          exact atEmpty
    · intro ratCarrier n _nUnary
      cases h : r n with
      | Empty =>
          simp only [RatConstStream]
          exact ratCarrier
      | e0 _ =>
          simp only [RatConstStream]
          exact ratCarrier
      | e1 _ =>
          simp only [RatConstStream]
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
          simp only [RatConstStream] at atEmpty
          exact atEmpty
      | e0 _ =>
          simp only [RatConstStream] at atEmpty
          exact atEmpty
      | e1 _ =>
          simp only [RatConstStream] at atEmpty
          exact atEmpty
    · intro ratClassifier
      exact And.intro (Iff.mpr carrierD ratClassifier.left)
        (And.intro (Iff.mpr carrierE ratClassifier.right.left)
          (fun n _nUnary => by
            cases h : r n with
            | Empty =>
                simp only [RatConstStream]
                exact ratClassifier
            | e0 _ =>
                simp only [RatConstStream]
                exact ratClassifier
            | e1 _ =>
                simp only [RatConstStream]
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
            simp only [RatConstStream] at atEmpty
            exact atEmpty
        | e0 _ =>
            simp only [RatConstStream] at atEmpty
            exact atEmpty
        | e1 _ =>
            simp only [RatConstStream] at atEmpty
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
            simp only [RatConstStream] at atEmpty
            exact atEmpty
        | e0 _ =>
            simp only [RatConstStream] at atEmpty
            exact atEmpty
        | e1 _ =>
            simp only [RatConstStream] at atEmpty
            exact atEmpty
      exact Iff.mpr RealConstantHistoryClassifier_e1_iff_rat ratClassifier
    · intro realClassifier n _nUnary
      have ratClassifier : RatHistoryClassifier d e :=
        Iff.mp RealConstantHistoryClassifier_e1_iff_rat realClassifier
      cases h : r n with
      | Empty =>
          simp only [RatConstStream]
          exact ratClassifier
      | e0 _ =>
          simp only [RatConstStream]
          exact ratClassifier
      | e1 _ =>
          simp only [RatConstStream]
          exact ratClassifier
  exact And.intro ratStreamIff (And.intro streamUnaryIff unaryRealIff)

theorem RealReindexedConstantStream_streamName_bridge {d e : BHist} {r : BHist -> BHist} :
    (RatHistoryClassifier d e ↔
      RatStreamNameClassifier (fun n => RatConstStream d (r n))
        (fun n => RatConstStream e (r n))) ∧
      (RatStreamNameClassifier (fun n => RatConstStream d (r n))
        (fun n => RatConstStream e (r n)) ↔
          RealUnaryStreamClassifier (fun n => RatConstStream d (r n))
            (fun n => RatConstStream e (r n))) ∧
        (RealUnaryStreamClassifier (fun n => RatConstStream d (r n))
          (fun n => RatConstStream e (r n)) ↔
            RealConstantHistoryClassifier (BHist.e1 d) (BHist.e1 e)) := by
  exact RealConstantStream_reindexed_streamName_bridge (d := d) (e := e) (r := r)

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
