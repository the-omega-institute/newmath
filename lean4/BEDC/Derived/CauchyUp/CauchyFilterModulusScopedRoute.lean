import BEDC.FKernel.Ask
import BEDC.FKernel.Hist
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Package.Core
import BEDC.FKernel.Unary.History

namespace BEDC.Derived.CauchyUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Hist
open BEDC.FKernel.Cont
open BEDC.FKernel.Package
open BEDC.FKernel.Unary
open BEDC.FKernel.NameCert

theorem CauchyFilterModulusScopedRoute [AskSetup] [PackageSetup]
    {S Q D R E H C P N streamRequest toleranceRead readbackRead sealRead
      structuralRead namedRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    UnaryHistory S -> UnaryHistory Q -> UnaryHistory D -> UnaryHistory R ->
      UnaryHistory E -> UnaryHistory H -> UnaryHistory C -> UnaryHistory P ->
        UnaryHistory N -> Cont S Q streamRequest -> Cont streamRequest D toleranceRead ->
          Cont toleranceRead R readbackRead -> Cont readbackRead E sealRead ->
            Cont H C structuralRead -> Cont P N namedRead -> PkgSig bundle P pkg ->
              PkgSig bundle N pkg ->
                SemanticNameCert
                    (fun row : BHist => hsame row sealRead ∧ UnaryHistory row)
                    (fun row : BHist =>
                      hsame row streamRequest ∨ hsame row toleranceRead ∨
                        hsame row readbackRead ∨ hsame row sealRead ∨
                          hsame row structuralRead ∨ hsame row namedRead)
                    (fun row : BHist =>
                      UnaryHistory row ∧ PkgSig bundle P pkg ∧ PkgSig bundle N pkg)
                    hsame ∧
                  UnaryHistory streamRequest ∧ UnaryHistory toleranceRead ∧
                    UnaryHistory readbackRead ∧ UnaryHistory sealRead ∧
                      UnaryHistory structuralRead ∧ UnaryHistory namedRead := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle Pkg PkgSig SemanticNameCert
  intro sUnary qUnary dUnary rUnary eUnary hUnary cUnary pUnary nUnary streamRoute
    toleranceRoute readbackRoute sealRoute structuralRoute namingRoute provenancePkg namePkg
  have streamUnary : UnaryHistory streamRequest :=
    unary_cont_closed sUnary qUnary streamRoute
  have toleranceUnary : UnaryHistory toleranceRead :=
    unary_cont_closed streamUnary dUnary toleranceRoute
  have readbackUnary : UnaryHistory readbackRead :=
    unary_cont_closed toleranceUnary rUnary readbackRoute
  have sealUnary : UnaryHistory sealRead :=
    unary_cont_closed readbackUnary eUnary sealRoute
  have structuralUnary : UnaryHistory structuralRead :=
    unary_cont_closed hUnary cUnary structuralRoute
  have namedUnary : UnaryHistory namedRead :=
    unary_cont_closed pUnary nUnary namingRoute
  have sourceSeal :
      (fun row : BHist => hsame row sealRead ∧ UnaryHistory row) sealRead := by
    exact ⟨hsame_refl sealRead, sealUnary⟩
  constructor
  · exact {
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
              unary_transport source.right sameRows⟩
      }
      pattern_sound := by
        intro _row source
        exact Or.inr (Or.inr (Or.inr (Or.inl source.left)))
      ledger_sound := by
        intro _row source
        exact ⟨source.right, provenancePkg, namePkg⟩
    }
  · exact
      ⟨streamUnary, toleranceUnary, readbackUnary, sealUnary, structuralUnary, namedUnary⟩

end BEDC.Derived.CauchyUp
