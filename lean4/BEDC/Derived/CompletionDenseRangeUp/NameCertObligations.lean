import BEDC.Derived.CompletionDenseRangeUp
import BEDC.FKernel.NameCert

namespace BEDC.Derived.CompletionDenseRangeUp

open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert

theorem CompletionDenseRangeCarrier_namecert_obligations
    (X : BEDC.Derived.CompletionDenseRangeUp) :
    hsame X.S X.S ∧ hsame X.D X.D ∧ hsame X.E X.E ∧ hsame X.N X.N ∧
      NameCert (fun row : BHist => hsame row X.N) hsame := by
  -- BEDC touchpoint anchor: BHist NameCert hsame
  refine
    ⟨hsame_refl X.S, hsame_refl X.D, hsame_refl X.E, hsame_refl X.N, ?_⟩
  exact {
    carrier_inhabited := Exists.intro X.N (hsame_refl X.N)
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
      exact hsame_trans (hsame_symm sameRows) source
  }

end BEDC.Derived.CompletionDenseRangeUp
