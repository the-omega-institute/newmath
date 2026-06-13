import BEDC.Derived.ClosedSubstitutionBoundaryUp.ConsumerExhaustion

namespace BEDC.Derived.ClosedSubstitutionBoundaryUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem ClosedSubstitutionBoundary_public_consumer_surface [AskSetup] [PackageSetup]
    {T D V K R Q H C P N substituteRead publicRead consumerRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    UnaryHistory T → UnaryHistory D → UnaryHistory V → UnaryHistory K → UnaryHistory R →
      UnaryHistory Q → UnaryHistory C → UnaryHistory N → Cont K Q substituteRead →
        Cont substituteRead C publicRead → Cont C N consumerRead → hsame H BHist.Empty →
          PkgSig bundle P pkg →
            SemanticNameCert
              (fun row : BHist => hsame row N ∧ UnaryHistory row)
              (fun row : BHist =>
                hsame row substituteRead ∨ hsame row publicRead ∨ hsame row consumerRead ∨
                  hsame row C ∨ hsame row N)
              (fun row : BHist =>
                UnaryHistory row ∧ Cont K Q substituteRead ∧
                  Cont substituteRead C publicRead ∧ Cont C N consumerRead ∧
                    PkgSig bundle P pkg)
              hsame ∧
              UnaryHistory substituteRead ∧ UnaryHistory publicRead ∧
                UnaryHistory consumerRead := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont SemanticNameCert hsame UnaryHistory
  intro _unaryT _unaryD _unaryV unaryK _unaryR unaryQ unaryC unaryN substituteRoute
    publicRoute consumerRoute _emptyTransport pkgSig
  have substituteUnary : UnaryHistory substituteRead :=
    unary_cont_closed unaryK unaryQ substituteRoute
  have publicUnary : UnaryHistory publicRead :=
    unary_cont_closed substituteUnary unaryC publicRoute
  have consumerUnary : UnaryHistory consumerRead :=
    unary_cont_closed unaryC unaryN consumerRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row N ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row substituteRead ∨ hsame row publicRead ∨ hsame row consumerRead ∨
              hsame row C ∨ hsame row N)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont K Q substituteRead ∧
              Cont substituteRead C publicRead ∧ Cont C N consumerRead ∧
                PkgSig bundle P pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro N ⟨hsame_refl N, unaryN⟩
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
      exact Or.inr (Or.inr (Or.inr (Or.inr source.left)))
    ledger_sound := by
      intro _row source
      exact ⟨source.right, substituteRoute, publicRoute, consumerRoute, pkgSig⟩
  }
  exact ⟨cert, substituteUnary, publicUnary, consumerUnary⟩

end BEDC.Derived.ClosedSubstitutionBoundaryUp
