import BEDC.FKernel.Hist
import BEDC.FKernel.Cont
import BEDC.Derived.LinearMapUp
import BEDC.Derived.CommRingUp
import BEDC.Derived.DeterminantUp

namespace BEDC.Derived.EigenUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Cont
open BEDC.Derived.LinearMapUp
open BEDC.Derived.CommRingUp
open BEDC.Derived.DeterminantUp

def EigenComponentSingletonCarrier (f lam v pair : BHist) : Prop :=
  LinearMapSingletonCarrier f ∧ CommRingSingletonCarrier lam ∧
    LinearMapSingletonCarrier v ∧ Cont lam v pair

theorem EigenSingletonCarrier_pair_empty_iff {f lam v pair : BHist} :
    EigenComponentSingletonCarrier f lam v pair ↔
      LinearMapSingletonCarrier f ∧ CommRingSingletonCarrier lam ∧
        LinearMapSingletonCarrier v ∧ hsame pair BHist.Empty := by
  constructor
  · intro carrier
    cases carrier with
    | intro fCarrier rest =>
        cases rest with
        | intro lamCarrier rest =>
            cases rest with
            | intro vCarrier contPair =>
                have pairEmpty : hsame pair BHist.Empty := by
                  have appendEmpty : hsame (append lam v) BHist.Empty :=
                    append_eq_empty_iff.mpr (And.intro lamCarrier vCarrier)
                  exact hsame_trans contPair appendEmpty
                exact And.intro fCarrier
                  (And.intro lamCarrier (And.intro vCarrier pairEmpty))
  · intro carrier
    cases carrier with
    | intro fCarrier rest =>
        cases rest with
        | intro lamCarrier rest =>
            cases rest with
            | intro vCarrier pairEmpty =>
                have appendEmpty : hsame (append lam v) BHist.Empty :=
                  append_eq_empty_iff.mpr (And.intro lamCarrier vCarrier)
                have contPair : Cont lam v pair :=
                  cont_intro (pairEmpty.trans appendEmpty.symm)
                exact And.intro fCarrier
                  (And.intro lamCarrier (And.intro vCarrier contPair))

def EigenSingletonCarrier (pair : BHist) : Prop :=
  ∃ map scalar vector : BHist,
    LinearMapSingletonCarrier map ∧
      DeterminantSingletonCarrier scalar ∧
        LinearMapSingletonCarrier vector ∧ Cont map (append scalar vector) pair

theorem EigenSingletonCarrier_cont_result_transport {map scalar vector pair pair' : BHist} :
    LinearMapSingletonCarrier map ->
      DeterminantSingletonCarrier scalar ->
        LinearMapSingletonCarrier vector ->
          Cont map (append scalar vector) pair -> hsame pair pair' ->
            EigenSingletonCarrier pair' := by
  intro mapCarrier scalarCarrier vectorCarrier contPair samePair
  exact Exists.intro map
    (Exists.intro scalar
      (Exists.intro vector
        (And.intro mapCarrier
          (And.intro scalarCarrier
            (And.intro vectorCarrier (cont_result_hsame_transport contPair samePair))))))

end BEDC.Derived.EigenUp
