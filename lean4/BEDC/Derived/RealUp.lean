import BEDC.Derived.RatUp
import BEDC.Derived.RatUp.HistoryClassifier

namespace BEDC.Derived.RealUp

open BEDC.FKernel.Hist
open BEDC.Derived.RatUp
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

def RealStreamClassifier (x y : Nat -> BHist) : Prop :=
  forall n : Nat, BEDC.Derived.RatUp.RatHistoryClassifier (x n) (y n)

def RealStreamPrefixClassifier (x y : Nat -> BHist) : Nat -> Prop :=
  Nat.rec
    (BEDC.Derived.RatUp.RatHistoryClassifier (x Nat.zero) (y Nat.zero))
    (fun n acc => And acc
      (BEDC.Derived.RatUp.RatHistoryClassifier (x (Nat.succ n)) (y (Nat.succ n))))

theorem RealStreamClassifier_prefix {x y : Nat -> BHist} :
    RealStreamClassifier x y -> forall n : Nat, RealStreamPrefixClassifier x y n := by
  intro classified n
  induction n with
  | zero =>
      exact classified Nat.zero
  | succ n ih =>
      exact And.intro ih (classified (Nat.succ n))

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

end BEDC.Derived.RealUp
