import BEDC.Derived.RealMetricUp
import BEDC.FKernel.NameCert

namespace BEDC.Derived.RealMetricUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem RealMetricCarrier_identity_of_indiscernibles_window [AskSetup] [PackageSetup]
    {X Y A D S R H C P N windowRead regularRead distanceRead zeroRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    RealMetricCarrier X Y A D S R H C P N bundle pkg ->
      Cont X S windowRead ->
        Cont windowRead R regularRead ->
          Cont regularRead A distanceRead ->
            Cont distanceRead N zeroRead ->
              PkgSig bundle zeroRead pkg ->
                SemanticNameCert
                    (fun row : BHist => hsame row zeroRead ∧ UnaryHistory row)
                    (fun row : BHist =>
                      hsame row X ∨ hsame row Y ∨ hsame row S ∨ hsame row R ∨
                        hsame row D ∨ hsame row A ∨ hsame row N ∨ hsame row zeroRead)
                    (fun row : BHist =>
                      UnaryHistory row ∧ Cont X S windowRead ∧
                        Cont windowRead R regularRead ∧ Cont regularRead A distanceRead ∧
                          Cont distanceRead N zeroRead ∧ PkgSig bundle zeroRead pkg)
                    hsame ∧
                  UnaryHistory windowRead ∧ UnaryHistory regularRead ∧
                    UnaryHistory distanceRead ∧ UnaryHistory zeroRead := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame SemanticNameCert UnaryHistory
  intro carrier windowRoute regularRoute distanceRoute zeroRoute zeroPkg
  have xUnary : UnaryHistory X := carrier.left
  have sUnary : UnaryHistory S := carrier.right.right.right.right.left
  have rUnary : UnaryHistory R := carrier.right.right.right.right.right.left
  have dUnary : UnaryHistory D := carrier.right.right.right.left
  have aUnary : UnaryHistory A := carrier.right.right.left
  have nUnary : UnaryHistory N :=
    carrier.right.right.right.right.right.right.right.right.right.left
  have windowUnary : UnaryHistory windowRead :=
    unary_cont_closed xUnary sUnary windowRoute
  have regularUnary : UnaryHistory regularRead :=
    unary_cont_closed windowUnary rUnary regularRoute
  have distanceUnary : UnaryHistory distanceRead :=
    unary_cont_closed regularUnary aUnary distanceRoute
  have zeroUnary : UnaryHistory zeroRead :=
    unary_cont_closed distanceUnary nUnary zeroRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row zeroRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row X ∨ hsame row Y ∨ hsame row S ∨ hsame row R ∨ hsame row D ∨
              hsame row A ∨ hsame row N ∨ hsame row zeroRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont X S windowRead ∧ Cont windowRead R regularRead ∧
              Cont regularRead A distanceRead ∧ Cont distanceRead N zeroRead ∧
                PkgSig bundle zeroRead pkg)
          hsame := {
    core := {
      carrier_inhabited :=
        Exists.intro zeroRead ⟨hsame_refl zeroRead, zeroUnary⟩
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
                    (Or.inr source.left))))))
    ledger_sound := by
      intro _row source
      exact
        ⟨source.right, windowRoute, regularRoute, distanceRoute, zeroRoute, zeroPkg⟩
  }
  exact ⟨cert, windowUnary, regularUnary, distanceUnary, zeroUnary⟩

end BEDC.Derived.RealMetricUp
