import BEDC.Derived.StreamNameUp

namespace BEDC.Derived.StreamNameUp

open BEDC.FKernel.Bundle
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Unary
open BEDC.Derived.RatUp

theorem StreamNamePublicInterfaceExportPackage
    {s t : BHist -> BHist} {bundle : ProbeBundle BHist} {windowRead : BHist} :
    RatStreamNameCarrier s ->
      RatStreamNameCarrier t ->
        RatStreamNameFiniteWindowClassifier s t bundle ->
          InBundle windowRead bundle ->
            UnaryHistory windowRead ->
              SemanticNameCert
                  (fun row : BHist => hsame row (s windowRead) ∧ RatHistoryCarrier row)
                  (fun row : BHist => hsame row (s windowRead) ∨ hsame row (t windowRead))
                  (fun row : BHist => RatHistoryClassifier row (t windowRead))
                  hsame ∧ RatHistoryClassifier (s windowRead) (t windowRead) := by
  -- BEDC touchpoint anchor: BHist ProbeBundle InBundle hsame SemanticNameCert RatHistoryCarrier
  intro carrierS _carrierT windowClassifier windowMember windowUnary
  have pointClassifier : RatHistoryClassifier (s windowRead) (t windowRead) :=
    windowClassifier windowRead windowMember windowUnary
  have source :
      (fun row : BHist => hsame row (s windowRead) ∧ RatHistoryCarrier row)
        (s windowRead) := by
    exact ⟨hsame_refl (s windowRead), carrierS windowRead windowUnary⟩
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row (s windowRead) ∧ RatHistoryCarrier row)
          (fun row : BHist => hsame row (s windowRead) ∨ hsame row (t windowRead))
          (fun row : BHist => RatHistoryClassifier row (t windowRead))
          hsame := by
    exact {
      core := {
        carrier_inhabited := Exists.intro (s windowRead) source
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
          intro _row _other sameRows sourceRows
          constructor
          · exact hsame_trans (hsame_symm sameRows) sourceRows.left
          · exact RatHistoryCarrier_hsame_transport sameRows sourceRows.right
      }
      pattern_sound := by
        intro _row sourceRows
        exact Or.inl sourceRows.left
      ledger_sound := by
        intro _row sourceRows
        cases sourceRows.left
        exact pointClassifier
    }
  exact ⟨cert, pointClassifier⟩

end BEDC.Derived.StreamNameUp
