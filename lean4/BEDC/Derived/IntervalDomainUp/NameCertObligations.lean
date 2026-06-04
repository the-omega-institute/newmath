import BEDC.Derived.IntervalDomainUp.TasteGate
import BEDC.FKernel.Cont
import BEDC.FKernel.NameCert

namespace BEDC.Derived.IntervalDomainUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert

theorem IntervalDomainNameCertObligations
    {L R N W Q E H C P A refinementRead directedRead endpointRead sealRead : BHist} :
    Cont L R refinementRead ->
      Cont refinementRead N directedRead ->
        Cont W Q endpointRead ->
          Cont directedRead endpointRead sealRead ->
            hsame H A ->
              SemanticNameCert
                  (fun row : BHist => hsame row sealRead ∧
                    (hsame row E ∨ hsame row sealRead))
                  (fun row : BHist =>
                    hsame row L ∨ hsame row R ∨ hsame row N ∨ hsame row W ∨
                      hsame row Q ∨ hsame row E ∨ hsame row sealRead)
                  (fun _row : BHist => Cont directedRead endpointRead sealRead ∧
                    hsame H A)
                  hsame := by
  -- BEDC touchpoint anchor: BHist Cont hsame SemanticNameCert NameCert
  intro _refinementRoute _directedRoute _endpointRoute sealRoute structuralSame
  have sourceSeal :
      (fun row : BHist => hsame row sealRead ∧ (hsame row E ∨ hsame row sealRead))
        sealRead := by
    exact ⟨hsame_refl sealRead, Or.inr (hsame_refl sealRead)⟩
  exact {
    core := {
      carrier_inhabited := Exists.intro sealRead sourceSeal
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
            Or.inr (hsame_trans (hsame_symm sameRows) source.left)⟩
    }
    pattern_sound := by
      intro _row source
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr source.left)))))
    ledger_sound := by
      intro _row _source
      exact ⟨sealRoute, structuralSame⟩
  }

end BEDC.Derived.IntervalDomainUp
