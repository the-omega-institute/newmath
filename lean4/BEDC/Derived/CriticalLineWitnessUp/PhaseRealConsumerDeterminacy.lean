import BEDC.Derived.CriticalLineWitnessUp

namespace BEDC.Derived.CriticalLineWitnessUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Unary

theorem CriticalLineWitnessCarrier_phase_real_consumer_determinacy
    {Z S M R Q H C P N dyadicFace streamFace regSeqRatFace realFace selectedFace : BHist} :
    CriticalLineWitnessCarrier Z S M R Q H C P N ->
      Cont (append Z S) Q selectedFace ->
        hsame selectedFace dyadicFace ∨ hsame selectedFace streamFace ∨
          hsame selectedFace regSeqRatFace ∨ hsame selectedFace realFace ->
          SemanticNameCert
              (fun row : BHist => hsame row selectedFace ∧ UnaryHistory row)
              (fun row : BHist =>
                hsame row dyadicFace ∨ hsame row streamFace ∨
                  hsame row regSeqRatFace ∨ hsame row realFace)
              (fun row : BHist => hsame row selectedFace ∧ Cont (append Z S) Q selectedFace)
              hsame ∧
            UnaryHistory selectedFace ∧ hsame H (append Z S) := by
  -- BEDC touchpoint anchor: CriticalLineWitnessCarrier BHist Cont hsame SemanticNameCert UnaryHistory
  intro packet selectedRoute selectedFaceChoice
  obtain ⟨unaryZ, unaryS, unaryM, unaryR, _unaryP, sameH, routeQ, _routeC, _routeN⟩ :=
    packet
  have unaryQ : UnaryHistory Q :=
    unary_cont_closed unaryM unaryR routeQ
  have appendUnary : UnaryHistory (append Z S) :=
    unary_cont_closed unaryZ unaryS (cont_intro rfl)
  have selectedUnary : UnaryHistory selectedFace :=
    unary_cont_closed appendUnary unaryQ selectedRoute
  have sourceAtSelected : hsame selectedFace selectedFace ∧ UnaryHistory selectedFace :=
    ⟨hsame_refl selectedFace, selectedUnary⟩
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row selectedFace ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row dyadicFace ∨ hsame row streamFace ∨
              hsame row regSeqRatFace ∨ hsame row realFace)
          (fun row : BHist => hsame row selectedFace ∧ Cont (append Z S) Q selectedFace)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro selectedFace sourceAtSelected
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
        intro _row _other sameRows source
        exact
          ⟨hsame_trans (hsame_symm sameRows) source.left,
            unary_transport source.right sameRows⟩
    }
    pattern_sound := by
      intro _row source
      cases selectedFaceChoice with
      | inl selectedIsDyadic =>
          exact Or.inl (hsame_trans source.left selectedIsDyadic)
      | inr remainingFaces =>
          cases remainingFaces with
          | inl selectedIsStream =>
              exact Or.inr (Or.inl (hsame_trans source.left selectedIsStream))
          | inr finalFaces =>
              cases finalFaces with
              | inl selectedIsRegSeqRat =>
                  exact
                    Or.inr
                      (Or.inr (Or.inl (hsame_trans source.left selectedIsRegSeqRat)))
              | inr selectedIsReal =>
                  exact
                    Or.inr
                      (Or.inr (Or.inr (hsame_trans source.left selectedIsReal)))
    ledger_sound := by
      intro _row source
      exact ⟨source.left, selectedRoute⟩
  }
  exact ⟨cert, selectedUnary, sameH⟩

end BEDC.Derived.CriticalLineWitnessUp
