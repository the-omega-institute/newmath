import BEDC.Derived.ContinuationMonadUp

namespace BEDC.Derived.ContinuationMonadUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem ContinuationMonadCarrier_category_boundary_readback_totality
    [AskSetup] [PackageSetup]
    {A B C f g u H K L N read : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ContinuationMonadCarrier A B C f g u H K L N ->
      Cont L N read ->
        PkgSig bundle read pkg ->
          UnaryHistory A ∧ UnaryHistory B ∧ UnaryHistory C ∧ UnaryHistory f ∧
            UnaryHistory g ∧ UnaryHistory u ∧ UnaryHistory K ∧ UnaryHistory L ∧
              UnaryHistory read ∧ Cont A f B ∧ Cont B g C ∧ Cont f g K ∧
                Cont K u L ∧ Cont L N read ∧ hsame N L ∧ PkgSig bundle read pkg ∧
                  SemanticNameCert
                    (fun row : BHist => hsame row read ∧ UnaryHistory row)
                    (fun row : BHist => hsame row read ∧ Cont L N read)
                    (fun row : BHist => hsame row read ∧ PkgSig bundle read pkg)
                    hsame := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont SemanticNameCert hsame UnaryHistory
  intro carrier routeRead readPkg
  obtain ⟨unaryA, unaryF, unaryG, unaryU, routeB, routeC, routeK, routeL,
    sameEndpoint⟩ := carrier
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
  have unaryRead : UnaryHistory read :=
    unary_cont_closed unaryL unaryN routeRead
  have sourceRead :
      (fun row : BHist => hsame row read ∧ UnaryHistory row) read := by
    exact ⟨hsame_refl read, unaryRead⟩
  have cert :
      SemanticNameCert
        (fun row : BHist => hsame row read ∧ UnaryHistory row)
        (fun row : BHist => hsame row read ∧ Cont L N read)
        (fun row : BHist => hsame row read ∧ PkgSig bundle read pkg)
        hsame := by
    exact {
      core := {
        carrier_inhabited := Exists.intro read sourceRead
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
          exact And.intro (hsame_trans (hsame_symm same) source.left)
            (unary_transport source.right same)
      }
      pattern_sound := by
        intro _row source
        exact ⟨source.left, routeRead⟩
      ledger_sound := by
        intro _row source
        exact ⟨source.left, readPkg⟩
    }
  exact
    ⟨unaryA, unaryB, unaryC, unaryF, unaryG, unaryU, unaryK, unaryL, unaryRead,
      routeB, routeC, routeK, routeL, routeRead, sameEndpoint, readPkg, cert⟩

end BEDC.Derived.ContinuationMonadUp
