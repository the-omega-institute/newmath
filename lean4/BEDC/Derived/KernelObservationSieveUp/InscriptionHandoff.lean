import BEDC.Derived.KernelObservationSieveUp.TasteGate
import BEDC.FKernel.NameCert

namespace BEDC.Derived.KernelObservationSieveUp

open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert

theorem KernelObservationSieve_inscription_handoff (k : KernelObservationSieveUp) :
    ∃ O S F A R T C P N : BHist,
      k = KernelObservationSieveUp.mk O S F A R T C P N ∧
        SemanticNameCert
          (fun row : BHist => hsame row N ∨ hsame row A ∨ hsame row R)
          (fun row : BHist =>
            hsame row O ∨ hsame row S ∨ hsame row F ∨ hsame row A ∨
              hsame row R ∨ hsame row T ∨ hsame row C ∨ hsame row P ∨ hsame row N)
          (fun row : BHist => hsame row N ∨ hsame row A ∨ hsame row R)
          hsame := by
  -- BEDC touchpoint anchor: BHist hsame SemanticNameCert
  cases k with
  | mk O S F A R T C P N =>
      have core :
          NameCert
            (fun row : BHist => hsame row N ∨ hsame row A ∨ hsame row R)
            hsame := {
        carrier_inhabited := Exists.intro N (Or.inl (hsame_refl N))
        equiv_refl := by
          intro row _source
          exact hsame_refl row
        equiv_symm := by
          intro _row _other sameRows
          exact hsame_symm sameRows
        equiv_trans := by
          intro _row _middle _other sameLeft sameRight
          exact hsame_trans sameLeft sameRight
        carrier_respects_equiv := by
          intro _row _other sameRows sourceRow
          cases sourceRow with
          | inl sameName =>
              exact Or.inl (hsame_trans (hsame_symm sameRows) sameName)
          | inr rest =>
              cases rest with
              | inl sameAccepted =>
                  exact Or.inr (Or.inl (hsame_trans (hsame_symm sameRows) sameAccepted))
              | inr sameRejected =>
                  exact Or.inr (Or.inr (hsame_trans (hsame_symm sameRows) sameRejected))
      }
      have patternSound :
          ∀ {row : BHist},
            (hsame row N ∨ hsame row A ∨ hsame row R) →
              hsame row O ∨ hsame row S ∨ hsame row F ∨ hsame row A ∨
                hsame row R ∨ hsame row T ∨ hsame row C ∨ hsame row P ∨
                  hsame row N := by
        intro _row sourceRow
        cases sourceRow with
        | inl sameName =>
            exact
              Or.inr
                (Or.inr
                  (Or.inr
                    (Or.inr
                      (Or.inr
                        (Or.inr
                          (Or.inr
                            (Or.inr
                              sameName)))))))
        | inr rest =>
            cases rest with
            | inl sameAccepted =>
                exact Or.inr (Or.inr (Or.inr (Or.inl sameAccepted)))
            | inr sameRejected =>
                exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl sameRejected))))
      have cert :
          SemanticNameCert
            (fun row : BHist => hsame row N ∨ hsame row A ∨ hsame row R)
            (fun row : BHist =>
              hsame row O ∨ hsame row S ∨ hsame row F ∨ hsame row A ∨
                hsame row R ∨ hsame row T ∨ hsame row C ∨ hsame row P ∨ hsame row N)
            (fun row : BHist => hsame row N ∨ hsame row A ∨ hsame row R)
            hsame :=
        SemanticNameCert.mk core patternSound (by
          intro _row sourceRow
          exact sourceRow)
      exact ⟨O, S, F, A, R, T, C, P, N, rfl, cert⟩

end BEDC.Derived.KernelObservationSieveUp
