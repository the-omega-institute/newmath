import BEDC.Derived.BaireCategoryUp.TasteGate
import BEDC.FKernel.Cont

namespace BEDC.Derived.BaireCategoryUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem BaireCategoryCarrier_finite_schedule_choice_free_induction [AskSetup] [PackageSetup]
    {B M D O R T H C P N baseRead denseRead openRead refinedRead threadRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    Cont B M baseRead →
      Cont baseRead D denseRead →
        Cont denseRead O openRead →
          Cont openRead R refinedRead →
            Cont refinedRead T threadRead →
              PkgSig bundle P pkg →
                PkgSig bundle threadRead pkg →
                  UnaryHistory B →
                    UnaryHistory M →
                      UnaryHistory D →
                        UnaryHistory O →
                          UnaryHistory R →
                            UnaryHistory T →
                              SemanticNameCert
                                  (fun row : BHist => hsame row threadRead ∧ UnaryHistory row)
                                  (fun row : BHist =>
                                    hsame row B ∨ hsame row M ∨ hsame row D ∨
                                      hsame row O ∨ hsame row R ∨ hsame row T ∨
                                        hsame row threadRead)
                                  (fun row : BHist =>
                                    UnaryHistory row ∧ PkgSig bundle P pkg ∧
                                      PkgSig bundle threadRead pkg ∧
                                        Cont refinedRead T threadRead)
                                  hsame ∧
                                UnaryHistory baseRead ∧ UnaryHistory denseRead ∧
                                  UnaryHistory openRead ∧ UnaryHistory refinedRead ∧
                                    UnaryHistory threadRead := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame SemanticNameCert UnaryHistory
  intro baseRoute denseRoute openRoute refinedRoute threadRoute packageP threadPkg
    baseUnary metricUnary denseUnary openUnary refinementUnary threadUnary
  have baseReadUnary : UnaryHistory baseRead :=
    unary_cont_closed baseUnary metricUnary baseRoute
  have denseReadUnary : UnaryHistory denseRead :=
    unary_cont_closed baseReadUnary denseUnary denseRoute
  have openReadUnary : UnaryHistory openRead :=
    unary_cont_closed denseReadUnary openUnary openRoute
  have refinedReadUnary : UnaryHistory refinedRead :=
    unary_cont_closed openReadUnary refinementUnary refinedRoute
  have threadReadUnary : UnaryHistory threadRead :=
    unary_cont_closed refinedReadUnary threadUnary threadRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row threadRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row B ∨ hsame row M ∨ hsame row D ∨ hsame row O ∨ hsame row R ∨
              hsame row T ∨ hsame row threadRead)
          (fun row : BHist =>
            UnaryHistory row ∧ PkgSig bundle P pkg ∧ PkgSig bundle threadRead pkg ∧
              Cont refinedRead T threadRead)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro threadRead ⟨hsame_refl threadRead, threadReadUnary⟩
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
      exact ⟨source.right, packageP, threadPkg, threadRoute⟩
  }
  exact
    ⟨cert, baseReadUnary, denseReadUnary, openReadUnary, refinedReadUnary,
      threadReadUnary⟩

end BEDC.Derived.BaireCategoryUp
