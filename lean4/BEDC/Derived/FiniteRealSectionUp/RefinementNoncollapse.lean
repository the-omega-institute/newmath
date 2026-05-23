import BEDC.Derived.FiniteRealSectionUp.TransportStability

namespace BEDC.Derived.FiniteRealSectionUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary
open BEDC.Meta.TasteGate

theorem FiniteRealSection_refinement_noncollapse [AskSetup] [PackageSetup]
    {q W R D E H C P N qW qWR qWRD qWRDE terminal refined ambient : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    UnaryHistory q → UnaryHistory W → UnaryHistory R → UnaryHistory D →
      UnaryHistory E → UnaryHistory N → UnaryHistory C → Cont q W qW →
        Cont qW R qWR → Cont qWR D qWRD → Cont qWRD E qWRDE →
          Cont qWRDE N terminal → Cont terminal C refined →
            PkgSig bundle refined pkg → hsame ambient (BHist.e0 refined) →
              UnaryHistory refined ∧
                FieldFaithful.fields (FiniteRealSectionUp.mk q W R D E H C P N) =
                  [q, W, R, D, E, H, C, P, N] ∧
                SemanticNameCert
                  (fun row : BHist => hsame row refined ∧ UnaryHistory row)
                  (fun row : BHist => hsame row terminal ∨ hsame row refined)
                  (fun row : BHist => hsame row refined ∧ PkgSig bundle refined pkg)
                  hsame ∧
                (hsame ambient refined → False) := by
  -- BEDC touchpoint anchor: BHist ProbeBundle PkgSig SemanticNameCert hsame Cont
  intro unaryQ unaryW unaryR unaryD unaryE unaryN unaryC requestWindow windowReadback
    readbackTolerance toleranceSeal sealTerminal terminalRefined refinedPkg ambientExtended
  have requestWindowUnary : UnaryHistory qW :=
    unary_cont_closed unaryQ unaryW requestWindow
  have windowReadbackUnary : UnaryHistory qWR :=
    unary_cont_closed requestWindowUnary unaryR windowReadback
  have readbackToleranceUnary : UnaryHistory qWRD :=
    unary_cont_closed windowReadbackUnary unaryD readbackTolerance
  have toleranceSealUnary : UnaryHistory qWRDE :=
    unary_cont_closed readbackToleranceUnary unaryE toleranceSeal
  have terminalUnary : UnaryHistory terminal :=
    unary_cont_closed toleranceSealUnary unaryN sealTerminal
  have refinedUnary : UnaryHistory refined :=
    unary_cont_closed terminalUnary unaryC terminalRefined
  have cert :
      SemanticNameCert
        (fun row : BHist => hsame row refined ∧ UnaryHistory row)
        (fun row : BHist => hsame row terminal ∨ hsame row refined)
        (fun row : BHist => hsame row refined ∧ PkgSig bundle refined pkg)
        hsame := {
    core := {
      carrier_inhabited := Exists.intro refined ⟨hsame_refl refined, refinedUnary⟩
      equiv_refl := by
        intro row _source
        exact hsame_refl row
      equiv_symm := by
        intro _row _other same
        exact hsame_symm same
      equiv_trans := by
        intro _row _middle _other sameLeft sameRight
        exact hsame_trans sameLeft sameRight
      carrier_respects_equiv := by
        intro _row _other same source
        cases same
        exact source
    }
    pattern_sound := by
      intro _row source
      exact Or.inr source.left
    ledger_sound := by
      intro _row source
      exact ⟨source.left, refinedPkg⟩
  }
  refine ⟨refinedUnary, rfl, cert, ?_⟩
  intro ambientRefined
  exact hsame_extension_self_absurd.left refined
    (hsame_trans (hsame_symm ambientExtended) ambientRefined)

end BEDC.Derived.FiniteRealSectionUp
