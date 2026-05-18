import BEDC.Derived.ContinuationMonadUp

namespace BEDC.Derived.ContinuationMonadUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem ContinuationMonadNameCertObligations [AskSetup] [PackageSetup]
    {A B C f g u H K L N routeRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ContinuationMonadCarrier A B C f g u H K L N ->
      Cont L N routeRead ->
        PkgSig bundle routeRead pkg ->
          SemanticNameCert
              (fun row : BHist =>
                ContinuationMonadCarrier A B C f g u H K L N ∧ hsame row L)
              (fun row : BHist => hsame row L ∧ UnaryHistory row)
              (fun row : BHist => PkgSig bundle routeRead pkg ∧ hsame row L)
              hsame ∧
            UnaryHistory A ∧ UnaryHistory B ∧ UnaryHistory C ∧ UnaryHistory f ∧
              UnaryHistory g ∧ UnaryHistory u ∧ UnaryHistory K ∧ UnaryHistory L ∧
                UnaryHistory routeRead ∧ Cont A f B ∧ Cont B g C ∧ Cont f g K ∧
                  Cont K u L ∧ Cont L N routeRead ∧ hsame N L ∧
                    PkgSig bundle routeRead pkg := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle Pkg SemanticNameCert hsame
  intro carrier routeReadCont routeReadPkg
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
  have routeReadUnary : UnaryHistory routeRead :=
    unary_cont_closed unaryL unaryN routeReadCont
  have carrierPacket : ContinuationMonadCarrier A B C f g u H K L N :=
    ⟨unaryA, unaryF, unaryG, unaryU, routeB, routeC, routeK, routeL, sameEndpoint⟩
  have cert :
      SemanticNameCert
          (fun row : BHist =>
            ContinuationMonadCarrier A B C f g u H K L N ∧ hsame row L)
          (fun row : BHist => hsame row L ∧ UnaryHistory row)
          (fun row : BHist => PkgSig bundle routeRead pkg ∧ hsame row L)
          hsame := by
    exact {
      core := {
        carrier_inhabited := Exists.intro L ⟨carrierPacket, hsame_refl L⟩
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
        exact
          ⟨source.right, unary_transport unaryL (hsame_symm source.right)⟩
      ledger_sound := by
        intro _row source
        exact ⟨routeReadPkg, source.right⟩
    }
  exact
    ⟨cert, unaryA, unaryB, unaryC, unaryF, unaryG, unaryU, unaryK, unaryL,
      routeReadUnary, routeB, routeC, routeK, routeL, routeReadCont, sameEndpoint,
      routeReadPkg⟩

end BEDC.Derived.ContinuationMonadUp
