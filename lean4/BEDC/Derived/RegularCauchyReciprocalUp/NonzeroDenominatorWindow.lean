import BEDC.Derived.RegularCauchyReciprocalUp.TailStability

namespace BEDC.Derived.RegularCauchyReciprocalUp.TasteGate

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem RegularCauchyReciprocalNonzeroDenominatorWindow [AskSetup] [PackageSetup]
    {Q A M W D B T E H C P N apartnessWindow reciprocalRead budgetRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    UnaryHistory Q ->
      UnaryHistory A ->
        UnaryHistory W ->
          UnaryHistory D ->
            Cont Q A apartnessWindow ->
              Cont apartnessWindow W reciprocalRead ->
                Cont reciprocalRead D budgetRead ->
                  PkgSig bundle P pkg ->
                    PkgSig bundle N pkg ->
                      SemanticNameCert
                          (fun row : BHist => hsame row budgetRead ∧ UnaryHistory row)
                          (fun row : BHist =>
                            hsame row Q ∨ hsame row A ∨ hsame row M ∨ hsame row W ∨
                              hsame row D ∨ hsame row B ∨ hsame row budgetRead)
                          (fun row : BHist =>
                            UnaryHistory row ∧ Cont Q A apartnessWindow ∧
                              Cont apartnessWindow W reciprocalRead ∧
                                Cont reciprocalRead D budgetRead ∧
                                  PkgSig bundle P pkg ∧ PkgSig bundle N pkg)
                          hsame ∧
                        UnaryHistory apartnessWindow ∧ UnaryHistory reciprocalRead ∧
                          UnaryHistory budgetRead := by
  -- BEDC touchpoint anchor: BHist Cont PkgSig ProbeBundle hsame UnaryHistory SemanticNameCert
  intro qUnary aUnary wUnary dUnary apartnessRoute reciprocalRoute budgetRoute
    provenancePkg namePkg
  have apartnessUnary : UnaryHistory apartnessWindow :=
    unary_cont_closed qUnary aUnary apartnessRoute
  have reciprocalUnary : UnaryHistory reciprocalRead :=
    unary_cont_closed apartnessUnary wUnary reciprocalRoute
  have budgetUnary : UnaryHistory budgetRead :=
    unary_cont_closed reciprocalUnary dUnary budgetRoute
  constructor
  · exact {
      core := {
        carrier_inhabited := Exists.intro budgetRead ⟨hsame_refl budgetRead, budgetUnary⟩
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
        exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr source.left)))))
      ledger_sound := by
        intro _row source
        exact
          ⟨source.right, apartnessRoute, reciprocalRoute, budgetRoute, provenancePkg,
            namePkg⟩
    }
  · exact ⟨apartnessUnary, reciprocalUnary, budgetUnary⟩

end BEDC.Derived.RegularCauchyReciprocalUp.TasteGate
