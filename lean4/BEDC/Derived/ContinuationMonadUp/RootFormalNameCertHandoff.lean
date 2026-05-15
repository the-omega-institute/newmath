import BEDC.Derived.ContinuationMonadUp

namespace BEDC.Derived.ContinuationMonadUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem ContinuationMonadCarrier_root_formal_namecert_handoff [AskSetup] [PackageSetup]
    {A B C f g u H K L N formal : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ContinuationMonadCarrier A B C f g u H K L N →
      Cont L N formal →
        PkgSig bundle formal pkg →
          SemanticNameCert
              (fun row : BHist =>
                ContinuationMonadCarrier A B C f g u H K L N ∧ hsame row N)
              (fun row : BHist => hsame row N ∧ Cont K u L ∧ Cont L N formal)
              (fun row : BHist => hsame row N ∧ PkgSig bundle formal pkg)
              hsame ∧
            UnaryHistory N ∧ UnaryHistory formal := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont SemanticNameCert hsame
  intro carrier formalRoute formalPkg
  obtain ⟨unaryA, unaryF, unaryG, unaryU, routeB, routeC, routeK, routeL,
    sameEndpoint⟩ := carrier
  have carrierPacket : ContinuationMonadCarrier A B C f g u H K L N :=
    ⟨unaryA, unaryF, unaryG, unaryU, routeB, routeC, routeK, routeL, sameEndpoint⟩
  have unaryK : UnaryHistory K :=
    unary_cont_closed unaryF unaryG routeK
  have unaryL : UnaryHistory L :=
    unary_cont_closed unaryK unaryU routeL
  have unaryN : UnaryHistory N :=
    unary_transport unaryL (hsame_symm sameEndpoint)
  have unaryFormal : UnaryHistory formal :=
    unary_cont_closed unaryL unaryN formalRoute
  have cert :
      SemanticNameCert
          (fun row : BHist =>
            ContinuationMonadCarrier A B C f g u H K L N ∧ hsame row N)
          (fun row : BHist => hsame row N ∧ Cont K u L ∧ Cont L N formal)
          (fun row : BHist => hsame row N ∧ PkgSig bundle formal pkg)
          hsame := by
    exact {
      core := {
        carrier_inhabited :=
          Exists.intro N ⟨carrierPacket, hsame_refl N⟩
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
          exact ⟨source.left, hsame_trans (hsame_symm same) source.right⟩
      }
      pattern_sound := by
        intro _row source
        exact ⟨source.right, routeL, formalRoute⟩
      ledger_sound := by
        intro _row source
        exact ⟨source.right, formalPkg⟩
    }
  exact ⟨cert, unaryN, unaryFormal⟩

end BEDC.Derived.ContinuationMonadUp
