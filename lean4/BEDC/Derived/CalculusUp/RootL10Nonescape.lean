import BEDC.Derived.CalculusUp.TasteGate
import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.CalculusUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem CalculusRootL10Nonescape [AskSetup] [PackageSetup]
    {E R D L J H C P N rootRead sealRead namedRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    UnaryHistory E ->
      UnaryHistory R ->
        UnaryHistory D ->
          UnaryHistory L ->
            UnaryHistory J ->
              UnaryHistory N ->
                Cont E R rootRead ->
                  Cont rootRead D sealRead ->
                    Cont sealRead N namedRead ->
                      PkgSig bundle P pkg ->
                        PkgSig bundle namedRead pkg ->
                          SemanticNameCert
                              (fun row : BHist => hsame row namedRead ∧ UnaryHistory row)
                              (fun row : BHist =>
                                hsame row E ∨ hsame row R ∨ hsame row D ∨ hsame row L ∨
                                  hsame row J ∨ hsame row namedRead)
                              (fun row : BHist =>
                                UnaryHistory row ∧ Cont E R rootRead ∧
                                  Cont rootRead D sealRead ∧ Cont sealRead N namedRead ∧
                                    PkgSig bundle P pkg ∧ PkgSig bundle namedRead pkg)
                              hsame ∧
                            UnaryHistory namedRead := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig hsame SemanticNameCert
  intro eUnary rUnary dUnary _lUnary _jUnary nUnary rootRoute sealRoute namedRoute
    provenancePkg namedPkg
  have rootUnary : UnaryHistory rootRead :=
    unary_cont_closed eUnary rUnary rootRoute
  have sealUnary : UnaryHistory sealRead :=
    unary_cont_closed rootUnary dUnary sealRoute
  have namedUnary : UnaryHistory namedRead :=
    unary_cont_closed sealUnary nUnary namedRoute
  constructor
  · exact {
      core := {
        carrier_inhabited :=
          Exists.intro namedRead ⟨hsame_refl namedRead, namedUnary⟩
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
        exact ⟨source.right, rootRoute, sealRoute, namedRoute, provenancePkg, namedPkg⟩
    }
  · exact namedUnary

end BEDC.Derived.CalculusUp
