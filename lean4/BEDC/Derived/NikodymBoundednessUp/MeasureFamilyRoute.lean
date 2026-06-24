import BEDC.Derived.NikodymBoundednessUp.TasteGate
import BEDC.FKernel.Cont
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.NikodymBoundednessUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem NikodymBoundednessMeasureFamilyRoute [AskSetup] [PackageSetup]
    {measure eventWindow family pointwise variation bound density regularity transport replay
      provenance localName variationRead boundRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    UnaryHistory measure ->
      UnaryHistory eventWindow ->
        UnaryHistory family ->
          UnaryHistory pointwise ->
            UnaryHistory variation ->
              UnaryHistory bound ->
                UnaryHistory replay ->
                  Cont measure eventWindow family ->
                    Cont family pointwise variationRead ->
                      Cont variationRead variation boundRead ->
                        Cont boundRead replay bound ->
                          PkgSig bundle provenance pkg ->
                            PkgSig bundle localName pkg ->
                              PkgSig bundle boundRead pkg ->
                                SemanticNameCert
                                    (fun row : BHist => hsame row boundRead ∧ UnaryHistory row)
                                    (fun row : BHist =>
                                      hsame row measure ∨ hsame row eventWindow ∨
                                        hsame row family ∨ hsame row pointwise ∨
                                          hsame row variation ∨ hsame row boundRead)
                                    (fun row : BHist =>
                                      UnaryHistory row ∧ Cont measure eventWindow family ∧
                                        Cont family pointwise variationRead ∧
                                          Cont variationRead variation boundRead ∧
                                            PkgSig bundle boundRead pkg)
                                    hsame ∧
                                  UnaryHistory variationRead ∧ UnaryHistory boundRead := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont UnaryHistory PkgSig hsame SemanticNameCert
  intro measureUnary eventWindowUnary familyUnary pointwiseUnary variationUnary _boundUnary
    _replayUnary measureRoute variationRoute boundRoute _replayRoute _provenancePkg
    _localNamePkg boundPkg
  have variationReadUnary : UnaryHistory variationRead :=
    unary_cont_closed familyUnary pointwiseUnary variationRoute
  have boundReadUnary : UnaryHistory boundRead :=
    unary_cont_closed variationReadUnary variationUnary boundRoute
  have sourceAtBound :
      (fun row : BHist => hsame row boundRead ∧ UnaryHistory row) boundRead :=
    ⟨hsame_refl boundRead, boundReadUnary⟩
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row boundRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row measure ∨ hsame row eventWindow ∨ hsame row family ∨
              hsame row pointwise ∨ hsame row variation ∨ hsame row boundRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont measure eventWindow family ∧
              Cont family pointwise variationRead ∧ Cont variationRead variation boundRead ∧
                PkgSig bundle boundRead pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro boundRead sourceAtBound
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
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr source.left))))
    ledger_sound := by
      intro _row source
      exact ⟨source.right, measureRoute, variationRoute, boundRoute, boundPkg⟩
  }
  exact ⟨cert, variationReadUnary, boundReadUnary⟩

end BEDC.Derived.NikodymBoundednessUp
