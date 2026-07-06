import BEDC.Derived.UpperHemicontinuityUp.TasteGate
import BEDC.FKernel.Hist

namespace BEDC.Derived

open BEDC.FKernel.Hist
open BEDC.Meta.TasteGate
open BEDC.Derived.UpperHemicontinuityUp

inductive BergeMaximumUp : Type where
  | packet
      (parameter feasibleGraph objective valueWindow maximumComparison transport replay provenance
        localName : BHist) :
      BergeMaximumUp
  deriving DecidableEq

theorem BergeMaximumUp_upper_hemicontinuity_boundary_support (packet : BergeMaximumUp) :
    ∃ boundary : UpperHemicontinuityUp,
      Nonempty (BHistCarrier UpperHemicontinuityUp) ∧
        Nonempty (ChapterTasteGate UpperHemicontinuityUp) ∧
          Nonempty (FieldFaithful UpperHemicontinuityUp) ∧
            Nonempty (Nontrivial UpperHemicontinuityUp) ∧
              FieldFaithful.fields boundary =
                match packet with
                | BergeMaximumUp.packet parameter feasibleGraph objective valueWindow
                    maximumComparison transport replay provenance localName =>
                    [parameter, objective, feasibleGraph, valueWindow, maximumComparison,
                      feasibleGraph, maximumComparison, transport, replay, provenance,
                      localName] := by
  have alignment := UpperHemicontinuityTasteGate_single_carrier_alignment
  obtain ⟨_decodeEmpty, carrierWitness, tasteWitness, faithfulWitness, nontrivialWitness⟩ :=
    alignment
  cases packet with
  | packet parameter feasibleGraph objective valueWindow maximumComparison transport replay
      provenance localName =>
      exact
        ⟨UpperHemicontinuityUp.mk parameter objective feasibleGraph valueWindow
            maximumComparison feasibleGraph maximumComparison transport replay provenance localName,
          carrierWitness, tasteWitness, faithfulWitness, nontrivialWitness, rfl⟩

end BEDC.Derived
