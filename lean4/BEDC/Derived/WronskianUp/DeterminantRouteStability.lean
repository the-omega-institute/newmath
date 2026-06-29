import BEDC.Derived.WronskianUp.TasteGate
import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.WronskianUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem WronskianCarrier_determinant_route_stability [AskSetup] [PackageSetup]
    {F D J Omega S R E H C P N determinantRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    WronskianObligationRowSpec F D J Omega S R E H C P N D →
      WronskianObligationRowSpec F D J Omega S R E H C P N J →
        UnaryHistory D →
          UnaryHistory J →
            Cont D J determinantRead →
              PkgSig bundle determinantRead pkg →
                SemanticNameCert
                  (fun row : BHist => hsame row determinantRead ∧ UnaryHistory row)
                  (fun row : BHist =>
                    hsame row F ∨ hsame row D ∨ hsame row J ∨ hsame row Omega ∨
                      hsame row determinantRead)
                  (fun row : BHist =>
                    UnaryHistory row ∧ Cont D J determinantRead ∧
                      PkgSig bundle determinantRead pkg)
                  hsame ∧ UnaryHistory determinantRead := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle Pkg PkgSig hsame SemanticNameCert UnaryHistory
  intro _dSpec _jSpec dUnary jUnary determinantRoute determinantPkg
  have determinantUnary : UnaryHistory determinantRead :=
    unary_cont_closed dUnary jUnary determinantRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row determinantRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row F ∨ hsame row D ∨ hsame row J ∨ hsame row Omega ∨
              hsame row determinantRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont D J determinantRead ∧ PkgSig bundle determinantRead pkg)
          hsame := {
    core := {
      carrier_inhabited :=
        Exists.intro determinantRead ⟨hsame_refl determinantRead, determinantUnary⟩
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
      repeat (first | exact source.left | apply Or.inr)
    ledger_sound := by
      intro _row source
      exact ⟨source.right, determinantRoute, determinantPkg⟩
  }
  exact ⟨cert, determinantUnary⟩

end BEDC.Derived.WronskianUp
