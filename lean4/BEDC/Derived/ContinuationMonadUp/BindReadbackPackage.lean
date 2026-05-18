import BEDC.Derived.ContinuationMonadUp

namespace BEDC.Derived.ContinuationMonadUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem ContinuationMonadCarrier_bind_readback_exhaustion
    [AskSetup] [PackageSetup]
    {A B C f g u H K L N bindRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ContinuationMonadCarrier A B C f g u H K L N ->
      Cont K N bindRead ->
        PkgSig bundle bindRead pkg ->
          UnaryHistory A ∧ UnaryHistory B ∧ UnaryHistory C ∧ UnaryHistory f ∧
            UnaryHistory g ∧ UnaryHistory u ∧ UnaryHistory K ∧ UnaryHistory L ∧
              UnaryHistory bindRead ∧ Cont A f B ∧ Cont B g C ∧ Cont f g K ∧
                Cont K u L ∧ Cont K N bindRead ∧ hsame N L ∧
                  PkgSig bundle bindRead pkg ∧
                    SemanticNameCert
                      (fun row : BHist => hsame row bindRead ∧ UnaryHistory row)
                      (fun row : BHist => hsame row bindRead)
                      (fun row : BHist => hsame row bindRead ∧ PkgSig bundle bindRead pkg)
                      hsame := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont SemanticNameCert hsame
  intro carrier bindRoute bindPkg
  obtain ⟨unaryA, unaryF, unaryG, unaryU, routeB, routeC, routeK, routeL,
    sameEndpoint⟩ := carrier
  have unaryB : UnaryHistory B := unary_cont_closed unaryA unaryF routeB
  have unaryC : UnaryHistory C := unary_cont_closed unaryB unaryG routeC
  have unaryK : UnaryHistory K := unary_cont_closed unaryF unaryG routeK
  have unaryL : UnaryHistory L := unary_cont_closed unaryK unaryU routeL
  have unaryN : UnaryHistory N := unary_transport unaryL (hsame_symm sameEndpoint)
  have unaryBindRead : UnaryHistory bindRead := unary_cont_closed unaryK unaryN bindRoute
  have sourceBind :
      (fun row : BHist => hsame row bindRead ∧ UnaryHistory row) bindRead := by
    exact ⟨hsame_refl bindRead, unaryBindRead⟩
  have cert :
      SemanticNameCert
        (fun row : BHist => hsame row bindRead ∧ UnaryHistory row)
        (fun row : BHist => hsame row bindRead)
        (fun row : BHist => hsame row bindRead ∧ PkgSig bundle bindRead pkg)
        hsame := by
    exact {
      core := {
        carrier_inhabited := Exists.intro bindRead sourceBind
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
        exact source.left
      ledger_sound := by
        intro _row source
        exact And.intro source.left bindPkg
    }
  exact
    ⟨unaryA, unaryB, unaryC, unaryF, unaryG, unaryU, unaryK, unaryL, unaryBindRead,
      routeB, routeC, routeK, routeL, bindRoute, sameEndpoint, bindPkg, cert⟩

theorem ContinuationMonadCarrier_finite_bind_readback_package
    [AskSetup] [PackageSetup]
    {A B C f g u H K L N bindRead finiteRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ContinuationMonadCarrier A B C f g u H K L N ->
      Cont K N bindRead ->
        Cont bindRead N finiteRead ->
          PkgSig bundle finiteRead pkg ->
            UnaryHistory A ∧ UnaryHistory B ∧ UnaryHistory C ∧ UnaryHistory f ∧
              UnaryHistory g ∧ UnaryHistory u ∧ UnaryHistory K ∧ UnaryHistory L ∧
                UnaryHistory bindRead ∧ UnaryHistory finiteRead ∧ Cont A f B ∧
                  Cont B g C ∧ Cont f g K ∧ Cont K u L ∧ Cont K N bindRead ∧
                    Cont bindRead N finiteRead ∧ hsame N L ∧
                      PkgSig bundle finiteRead pkg ∧
                        SemanticNameCert
                          (fun row : BHist => hsame row finiteRead ∧ UnaryHistory row)
                          (fun row : BHist => hsame row finiteRead)
                          (fun row : BHist =>
                            hsame row finiteRead ∧ PkgSig bundle finiteRead pkg)
                          hsame := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont SemanticNameCert hsame
  intro carrier bindRoute finiteRoute finitePkg
  obtain ⟨unaryA, unaryF, unaryG, unaryU, routeB, routeC, routeK, routeL,
    sameEndpoint⟩ := carrier
  have unaryB : UnaryHistory B := unary_cont_closed unaryA unaryF routeB
  have unaryC : UnaryHistory C := unary_cont_closed unaryB unaryG routeC
  have unaryK : UnaryHistory K := unary_cont_closed unaryF unaryG routeK
  have unaryL : UnaryHistory L := unary_cont_closed unaryK unaryU routeL
  have unaryN : UnaryHistory N := unary_transport unaryL (hsame_symm sameEndpoint)
  have unaryBindRead : UnaryHistory bindRead := unary_cont_closed unaryK unaryN bindRoute
  have unaryFiniteRead : UnaryHistory finiteRead :=
    unary_cont_closed unaryBindRead unaryN finiteRoute
  have sourceFinite :
      (fun row : BHist => hsame row finiteRead ∧ UnaryHistory row) finiteRead := by
    exact ⟨hsame_refl finiteRead, unaryFiniteRead⟩
  have cert :
      SemanticNameCert
        (fun row : BHist => hsame row finiteRead ∧ UnaryHistory row)
        (fun row : BHist => hsame row finiteRead)
        (fun row : BHist => hsame row finiteRead ∧ PkgSig bundle finiteRead pkg)
        hsame := by
    exact {
      core := {
        carrier_inhabited := Exists.intro finiteRead sourceFinite
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
        exact source.left
      ledger_sound := by
        intro _row source
        exact And.intro source.left finitePkg
    }
  exact
    ⟨unaryA, unaryB, unaryC, unaryF, unaryG, unaryU, unaryK, unaryL, unaryBindRead,
      unaryFiniteRead, routeB, routeC, routeK, routeL, bindRoute, finiteRoute,
      sameEndpoint, finitePkg, cert⟩

end BEDC.Derived.ContinuationMonadUp
