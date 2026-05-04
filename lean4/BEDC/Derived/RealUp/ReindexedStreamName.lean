import BEDC.Derived.RealUp

namespace BEDC.Derived.RealUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Unary
open BEDC.Derived.RatUp
open BEDC.Derived.StreamNameUp

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

end BEDC.Derived.RealUp
