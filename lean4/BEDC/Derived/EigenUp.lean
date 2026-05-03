import BEDC.FKernel.Hist
import BEDC.FKernel.Cont
import BEDC.Derived.LinearMapUp
import BEDC.Derived.CommRingUp

namespace BEDC.Derived.EigenUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Cont
open BEDC.Derived.LinearMapUp
open BEDC.Derived.CommRingUp

def EigenSingletonCarrier (f lam v pair : BHist) : Prop :=
  LinearMapSingletonCarrier f ∧ CommRingSingletonCarrier lam ∧
    LinearMapSingletonCarrier v ∧ Cont lam v pair

theorem EigenSingletonCarrier_pair_empty_iff {f lam v pair : BHist} :
    EigenSingletonCarrier f lam v pair ↔
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

end BEDC.Derived.EigenUp
