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

theorem BaireCategory_finite_meet_density_handoff [AskSetup] [PackageSetup]
    {B M D O R T H C P N meetRead denseRead threadRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    Cont D O denseRead →
      Cont R T threadRead →
        Cont denseRead R meetRead →
          PkgSig bundle P pkg →
            PkgSig bundle meetRead pkg →
              UnaryHistory D →
                UnaryHistory O →
                  UnaryHistory R →
                    UnaryHistory T →
                      UnaryHistory denseRead ∧ UnaryHistory threadRead ∧
                        UnaryHistory meetRead ∧ Cont D O denseRead ∧
                          Cont R T threadRead ∧ Cont denseRead R meetRead ∧
                            PkgSig bundle P pkg ∧ PkgSig bundle meetRead pkg ∧
                              baireCategoryFields (BaireCategoryUp.mk B M D O R T H C P N) =
                                [B, M, D, O, R, T, H, C, P, N] := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont UnaryHistory PkgSig
  intro denseRoute threadRoute meetRoute packageP meetPkg denseUnary openUnary refinementUnary
    threadUnary
  have denseReadUnary : UnaryHistory denseRead :=
    unary_cont_closed denseUnary openUnary denseRoute
  have threadReadUnary : UnaryHistory threadRead :=
    unary_cont_closed refinementUnary threadUnary threadRoute
  have meetReadUnary : UnaryHistory meetRead :=
    unary_cont_closed denseReadUnary refinementUnary meetRoute
  exact
    ⟨denseReadUnary, threadReadUnary, meetReadUnary, denseRoute, threadRoute, meetRoute,
      packageP, meetPkg, rfl⟩

theorem BaireCategoryCarrier_finite_meet_density_handoff [AskSetup] [PackageSetup]
    {B M D O R T H C P N denseRead threadRead limitRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    Cont D O denseRead →
      Cont R T threadRead →
        Cont threadRead M limitRead →
          PkgSig bundle P pkg →
            UnaryHistory D →
              UnaryHistory O →
                UnaryHistory R →
                  UnaryHistory T →
                    UnaryHistory M →
                      SemanticNameCert
                        (fun row : BHist =>
                          hsame row denseRead ∨ hsame row threadRead ∨ hsame row limitRead)
                        (fun row : BHist => UnaryHistory row)
                        (fun row : BHist => PkgSig bundle P pkg ∨ PkgSig bundle row pkg)
                        hsame := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame SemanticNameCert UnaryHistory
  intro denseRoute threadRoute limitRoute packageP denseUnary openUnary refinementUnary
    threadUnary metricUnary
  have denseReadUnary : UnaryHistory denseRead :=
    unary_cont_closed denseUnary openUnary denseRoute
  have threadReadUnary : UnaryHistory threadRead :=
    unary_cont_closed refinementUnary threadUnary threadRoute
  have limitReadUnary : UnaryHistory limitRead :=
    unary_cont_closed threadReadUnary metricUnary limitRoute
  exact {
    core := {
      carrier_inhabited := Exists.intro denseRead (Or.inl (hsame_refl denseRead))
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
        cases source with
        | inl sameDense =>
            exact Or.inl (hsame_trans (hsame_symm sameRows) sameDense)
        | inr rest =>
            cases rest with
            | inl sameThread =>
                exact Or.inr (Or.inl (hsame_trans (hsame_symm sameRows) sameThread))
            | inr sameLimit =>
                exact Or.inr (Or.inr (hsame_trans (hsame_symm sameRows) sameLimit))
    }
    pattern_sound := by
      intro _row source
      cases source with
      | inl sameDense =>
          exact unary_transport denseReadUnary (hsame_symm sameDense)
      | inr rest =>
          cases rest with
          | inl sameThread =>
              exact unary_transport threadReadUnary (hsame_symm sameThread)
          | inr sameLimit =>
              exact unary_transport limitReadUnary (hsame_symm sameLimit)
    ledger_sound := by
      intro _row _source
      exact Or.inl packageP
  }

end BEDC.Derived.BaireCategoryUp
