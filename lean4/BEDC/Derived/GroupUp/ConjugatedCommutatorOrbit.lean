import BEDC.Derived.GroupUp

namespace BEDC.Derived.GroupUp
open BEDC.FKernel.Hist BEDC.FKernel.Cont

theorem GroupSingletonClassifier_conjugated_commutator_orbit_invariance {s x y : BHist} :
    GroupSingletonCarrier s -> GroupSingletonCarrier x -> GroupSingletonCarrier y ->
      let comm := fun p q : BHist => append (append (append p q) BHist.Empty) BHist.Empty
      let conj := fun a z : BHist => append (append a z) BHist.Empty
      let Orbit := fun p q : BHist => Exists (fun t : BHist =>
        GroupSingletonCarrier t ∧
          GroupSingletonClassifier (append (append t p) BHist.Empty) q)
      Orbit (comm (conj s x) (conj s y)) (comm x y) ∧
        Orbit (comm x y) (comm (conj s x) (conj s y)) := by
  intro carrierS carrierX carrierY
  cases carrierS
  cases carrierX
  cases carrierY
  constructor
  · exact ⟨BHist.Empty, rfl, rfl, rfl, rfl⟩
  · exact ⟨BHist.Empty, rfl, rfl, rfl, rfl⟩

end BEDC.Derived.GroupUp
