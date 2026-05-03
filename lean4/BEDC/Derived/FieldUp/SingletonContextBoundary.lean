import BEDC.Derived.FieldUp

namespace BEDC.Derived.FieldUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Cont
open BEDC.FKernel.NameCert

theorem ratup_fieldup_canonical_exit_singleton_context_boundary {L R h k : BHist} :
    FieldSingletonCarrier L -> FieldSingletonCarrier R ->
      SemanticNameCert
        (fun x : BHist => FieldSingletonCarrier (append L (append x R)))
        (fun x : BHist => FieldSingletonCarrier (append L (append x R)))
        (fun x : BHist => FieldSingletonCarrier (append L (append x R)))
        (fun x y : BHist =>
          FieldSingletonClassifier (append L (append x R)) (append L (append y R))) ∧
        (FieldSingletonCarrier (append L (append h R)) ↔ FieldSingletonCarrier h) ∧
          (FieldSingletonClassifier (append L (append h R)) (append L (append k R)) ↔
            FieldSingletonClassifier h k) := by
  intro carrierL carrierR
  have carrierContext :
      ∀ {x : BHist}, FieldSingletonCarrier (append L (append x R)) ↔
        FieldSingletonCarrier x := by
    intro x
    constructor
    · intro contextual
      have outer := append_eq_empty_iff.mp contextual
      have inner := append_eq_empty_iff.mp outer.right
      exact inner.left
    · intro carrierX
      have inner : FieldSingletonCarrier (append x R) :=
        append_eq_empty_iff.mpr (And.intro carrierX carrierR)
      exact append_eq_empty_iff.mpr (And.intro carrierL inner)
  have emptyContext : FieldSingletonCarrier (append L (append BHist.Empty R)) :=
    Iff.mpr carrierContext (hsame_refl BHist.Empty)
  refine ⟨?_, carrierContext, ?_⟩
  · exact {
      core := {
        carrier_inhabited := Exists.intro BHist.Empty emptyContext
        equiv_refl := by
          intro x carrierX
          exact And.intro carrierX (And.intro carrierX (hsame_refl (append L (append x R))))
        equiv_symm := by
          intro x y classified
          exact And.intro classified.right.left
            (And.intro classified.left (hsame_symm classified.right.right))
        equiv_trans := by
          intro x y z classifiedXY classifiedYZ
          exact And.intro classifiedXY.left
            (And.intro classifiedYZ.right.left
              (hsame_trans classifiedXY.right.right classifiedYZ.right.right))
        carrier_respects_equiv := by
          intro x y classified _carrierX
          exact classified.right.left
      }
      pattern_sound := by
        intro x source
        exact source
      ledger_sound := by
        intro x source
        exact source
    }
  · constructor
    · intro classified
      have carrierH : FieldSingletonCarrier h := Iff.mp carrierContext classified.left
      have carrierK : FieldSingletonCarrier k := Iff.mp carrierContext classified.right.left
      exact And.intro carrierH (And.intro carrierK (hsame_trans carrierH (hsame_symm carrierK)))
    · intro classified
      have carrierH : FieldSingletonCarrier (append L (append h R)) :=
        Iff.mpr carrierContext classified.left
      have carrierK : FieldSingletonCarrier (append L (append k R)) :=
        Iff.mpr carrierContext classified.right.left
      exact And.intro carrierH (And.intro carrierK (hsame_trans carrierH (hsame_symm carrierK)))

end BEDC.Derived.FieldUp
