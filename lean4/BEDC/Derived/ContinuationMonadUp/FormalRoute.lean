import BEDC.Derived.ContinuationMonadUp

namespace BEDC.Derived.ContinuationMonadUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem ContinuationMonadCarrier_root_formal_namecert_consumer_lock
    [AskSetup] [PackageSetup]
    {A B C f g u H K L N audit formal : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ContinuationMonadCarrier A B C f g u H K L N ->
      Cont L N audit ->
        Cont K N formal ->
          PkgSig bundle formal pkg ->
            SemanticNameCert
              (fun row : BHist =>
                ContinuationMonadCarrier A B C f g u H K L N ∧ Cont L N audit ∧
                  Cont K N formal ∧ hsame row formal)
              (fun row : BHist => hsame row formal ∧ Cont K N formal)
              (fun row : BHist => UnaryHistory row ∧ PkgSig bundle formal pkg ∧ hsame N L)
              hsame := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont SemanticNameCert hsame
  intro carrier auditRoute formalRoute formalPkg
  obtain ⟨unaryA, unaryF, unaryG, unaryU, routeB, routeC, routeK, routeL,
    sameEndpoint⟩ := carrier
  have carrierPacket : ContinuationMonadCarrier A B C f g u H K L N :=
    ⟨unaryA, unaryF, unaryG, unaryU, routeB, routeC, routeK, routeL, sameEndpoint⟩
  have unaryB : UnaryHistory B :=
    unary_cont_closed unaryA unaryF routeB
  have unaryC : UnaryHistory C :=
    unary_cont_closed unaryB unaryG routeC
  have unaryK : UnaryHistory K :=
    unary_cont_closed unaryF unaryG routeK
  have unaryL : UnaryHistory L :=
    unary_cont_closed unaryK unaryU routeL
  have unaryN : UnaryHistory N :=
    unary_transport unaryL (hsame_symm sameEndpoint)
  have unaryFormal : UnaryHistory formal :=
    unary_cont_closed unaryK unaryN formalRoute
  exact {
    core := {
      carrier_inhabited :=
        Exists.intro formal
          ⟨carrierPacket, auditRoute, formalRoute, hsame_refl formal⟩
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
        exact
          ⟨source.left, source.right.left, source.right.right.left,
            hsame_trans (hsame_symm same) source.right.right.right⟩
    }
    pattern_sound := by
      intro _row source
      exact ⟨source.right.right.right, source.right.right.left⟩
    ledger_sound := by
      intro _row source
      exact
        ⟨unary_transport_symm unaryFormal source.right.right.right, formalPkg,
          sameEndpoint⟩
  }

end BEDC.Derived.ContinuationMonadUp
