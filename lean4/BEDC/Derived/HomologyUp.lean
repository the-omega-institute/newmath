import BEDC.FKernel.Hist
import BEDC.FKernel.NameCert
import BEDC.FKernel.Cont

namespace BEDC.Derived.HomologyUp

open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Cont

def HomologySingletonCycleCarrier (h : BHist) : Prop :=
  hsame h BHist.Empty

def HomologySingletonCycleClassifier (h k : BHist) : Prop :=
  HomologySingletonCycleCarrier h ∧ HomologySingletonCycleCarrier k ∧ hsame h k

theorem HomologySingletonCycle_semanticNameCert :
    SemanticNameCert HomologySingletonCycleCarrier HomologySingletonCycleCarrier
      HomologySingletonCycleCarrier HomologySingletonCycleClassifier := by
  exact {
    core := {
      carrier_inhabited := Exists.intro BHist.Empty (hsame_refl BHist.Empty)
      equiv_refl := by
        intro h carrier
        exact And.intro carrier (And.intro carrier (hsame_refl h))
      equiv_symm := by
        intro h k classified
        exact And.intro classified.right.left
          (And.intro classified.left (hsame_symm classified.right.right))
      equiv_trans := by
        intro h k r classifiedHK classifiedKR
        exact And.intro classifiedHK.left
          (And.intro classifiedKR.right.left
            (hsame_trans classifiedHK.right.right classifiedKR.right.right))
      carrier_respects_equiv := by
        intro h k classified _carrier
        exact classified.right.left
    }
    pattern_sound := by
      intro _h source
      exact source
    ledger_sound := by
      intro _h source
      exact source
  }

def HomologyCycleCarrier (d : BHist -> BHist) (h : BHist) : Prop :=
  hsame (d h) BHist.Empty

def HomologyBoundaryCarrier (d : BHist -> BHist) (h : BHist) : Prop :=
  Exists (fun u : BHist => hsame h (d u))

theorem HomologyCycleCarrier_append_closed {d : BHist -> BHist}
    (dAppend : forall u v : BHist, hsame (d (append u v)) (append (d u) (d v)))
    {h k : BHist} :
    HomologyCycleCarrier d h -> HomologyCycleCarrier d k ->
      HomologyCycleCarrier d (append h k) := by
  intro cycleH cycleK
  exact hsame_trans (dAppend h k) (by
    have dhEmpty : d h = BHist.Empty := hsame_empty_iff.mp cycleH
    have dkEmpty : d k = BHist.Empty := hsame_empty_iff.mp cycleK
    exact append_eq_empty_iff.mpr (And.intro dhEmpty dkEmpty))

theorem HomologyBoundaryCarrier_append_closed {d : BHist -> BHist}
    (dAppend : forall u v : BHist, hsame (d (append u v)) (append (d u) (d v)))
    {h k : BHist} :
    HomologyBoundaryCarrier d h -> HomologyBoundaryCarrier d k ->
      HomologyBoundaryCarrier d (append h k) := by
  intro boundaryH boundaryK
  cases boundaryH with
  | intro u witnessH =>
      cases boundaryK with
      | intro v witnessK =>
          have appendWitness : hsame (append h k) (append (d u) (d v)) := by
            cases witnessH
            cases witnessK
            exact hsame_refl (append (d u) (d v))
          exact Exists.intro (append u v)
            (hsame_trans appendWitness (hsame_symm (dAppend u v)))

end BEDC.Derived.HomologyUp
