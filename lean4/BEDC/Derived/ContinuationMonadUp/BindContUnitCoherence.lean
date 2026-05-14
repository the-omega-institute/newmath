import BEDC.Derived.ContinuationMonadUp

namespace BEDC.Derived.ContinuationMonadUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem ContinuationMonadCarrier_bind_cont_unit_coherence
    [AskSetup] [PackageSetup]
    {A B C f g u H K L N category generator unitRead bindRead : BHist}
    {bundle : ProbeBundle ProbeName} {generatorPkg bindPkg : Pkg} :
    ContinuationMonadCarrier A B C f g u H K L N →
      Cont L N category →
        Cont category N generator →
          Cont u f unitRead →
            Cont K N bindRead →
              PkgSig bundle generator generatorPkg →
                PkgSig bundle bindRead bindPkg →
                  UnaryHistory A ∧ UnaryHistory B ∧ UnaryHistory C ∧ UnaryHistory f ∧
                    UnaryHistory g ∧ UnaryHistory u ∧ UnaryHistory K ∧ UnaryHistory L ∧
                      UnaryHistory category ∧ UnaryHistory generator ∧
                        UnaryHistory unitRead ∧ UnaryHistory bindRead ∧ Cont L N category ∧
                          Cont category N generator ∧ Cont u f unitRead ∧
                            Cont K N bindRead ∧ hsame N L ∧
                              PkgSig bundle generator generatorPkg ∧
                                PkgSig bundle bindRead bindPkg ∧
                                  SemanticNameCert
                                    (fun row : BHist => hsame row bindRead ∧ UnaryHistory row)
                                    (fun row : BHist => hsame row bindRead)
                                    (fun row : BHist =>
                                      hsame row bindRead ∧ PkgSig bundle bindRead bindPkg)
                                    hsame := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont SemanticNameCert hsame
  intro carrier categoryRoute generatorRoute unitRoute bindRoute generatorSig bindSig
  obtain ⟨unaryA, unaryF, unaryG, unaryU, routeB, routeC, routeK, routeL,
    sameEndpoint⟩ := carrier
  have unaryB : UnaryHistory B := unary_cont_closed unaryA unaryF routeB
  have unaryC : UnaryHistory C := unary_cont_closed unaryB unaryG routeC
  have unaryK : UnaryHistory K := unary_cont_closed unaryF unaryG routeK
  have unaryL : UnaryHistory L := unary_cont_closed unaryK unaryU routeL
  have unaryN : UnaryHistory N := unary_transport unaryL (hsame_symm sameEndpoint)
  have unaryCategory : UnaryHistory category :=
    unary_cont_closed unaryL unaryN categoryRoute
  have unaryGenerator : UnaryHistory generator :=
    unary_cont_closed unaryCategory unaryN generatorRoute
  have unaryUnitRead : UnaryHistory unitRead := unary_cont_closed unaryU unaryF unitRoute
  have unaryBindRead : UnaryHistory bindRead := unary_cont_closed unaryK unaryN bindRoute
  have sourceBind :
      (fun row : BHist => hsame row bindRead ∧ UnaryHistory row) bindRead := by
    exact ⟨hsame_refl bindRead, unaryBindRead⟩
  have cert :
      SemanticNameCert
        (fun row : BHist => hsame row bindRead ∧ UnaryHistory row)
        (fun row : BHist => hsame row bindRead)
        (fun row : BHist => hsame row bindRead ∧ PkgSig bundle bindRead bindPkg)
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
        exact And.intro source.left bindSig
    }
  exact
    ⟨unaryA, unaryB, unaryC, unaryF, unaryG, unaryU, unaryK, unaryL, unaryCategory,
      unaryGenerator, unaryUnitRead, unaryBindRead, categoryRoute, generatorRoute,
      unitRoute, bindRoute, sameEndpoint, generatorSig, bindSig, cert⟩

end BEDC.Derived.ContinuationMonadUp
