import BEDC.Derived.BishopRealRegularCompletionUp.TasteGate
import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.BishopRealRegularCompletionUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem BishopRealRegularCompletionCarrier_finite_means_route [AskSetup] [PackageSetup]
    {D S R M E H C P N windowRead readbackRead rateRead sealRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    (UnaryHistory D ∧ UnaryHistory S ∧ UnaryHistory R ∧ UnaryHistory M ∧ UnaryHistory E) →
      Cont D S windowRead →
        Cont windowRead R readbackRead →
          Cont readbackRead M rateRead →
            Cont rateRead E sealRead →
              PkgSig bundle P pkg →
                PkgSig bundle N pkg →
                  SemanticNameCert
                      (fun row : BHist => hsame row sealRead ∧ UnaryHistory row)
                      (fun row : BHist =>
                        hsame row D ∨ hsame row S ∨ hsame row R ∨ hsame row M ∨
                          hsame row E ∨ hsame row windowRead ∨ hsame row readbackRead ∨
                            hsame row rateRead ∨ hsame row sealRead)
                      (fun row : BHist =>
                        UnaryHistory row ∧ Cont D S windowRead ∧
                          Cont windowRead R readbackRead ∧ Cont readbackRead M rateRead ∧
                            Cont rateRead E sealRead ∧ PkgSig bundle P pkg ∧
                              PkgSig bundle N pkg)
                      hsame ∧
                    UnaryHistory windowRead ∧ UnaryHistory readbackRead ∧
                      UnaryHistory rateRead ∧ UnaryHistory sealRead := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig hsame SemanticNameCert
  intro rows windowRoute readbackRoute rateRoute sealRoute provenancePkg namePkg
  obtain ⟨dUnary, sUnary, rUnary, mUnary, eUnary⟩ := rows
  have windowUnary : UnaryHistory windowRead :=
    unary_cont_closed dUnary sUnary windowRoute
  have readbackUnary : UnaryHistory readbackRead :=
    unary_cont_closed windowUnary rUnary readbackRoute
  have rateUnary : UnaryHistory rateRead :=
    unary_cont_closed readbackUnary mUnary rateRoute
  have sealUnary : UnaryHistory sealRead :=
    unary_cont_closed rateUnary eUnary sealRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row sealRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row D ∨ hsame row S ∨ hsame row R ∨ hsame row M ∨
              hsame row E ∨ hsame row windowRead ∨ hsame row readbackRead ∨
                hsame row rateRead ∨ hsame row sealRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont D S windowRead ∧ Cont windowRead R readbackRead ∧
              Cont readbackRead M rateRead ∧ Cont rateRead E sealRead ∧
                PkgSig bundle P pkg ∧ PkgSig bundle N pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro sealRead ⟨hsame_refl sealRead, sealUnary⟩
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
      exact
        Or.inr
          (Or.inr
            (Or.inr
              (Or.inr
                (Or.inr
                  (Or.inr
                    (Or.inr
                      (Or.inr source.left)))))))
    ledger_sound := by
      intro _row source
      exact
        ⟨source.right, windowRoute, readbackRoute, rateRoute, sealRoute, provenancePkg,
          namePkg⟩
  }
  exact ⟨cert, windowUnary, readbackUnary, rateUnary, sealUnary⟩

end BEDC.Derived.BishopRealRegularCompletionUp
