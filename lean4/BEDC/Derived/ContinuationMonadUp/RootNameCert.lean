import BEDC.Derived.ContinuationMonadUp

namespace BEDC.Derived.ContinuationMonadUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem ContinuationMonadCarrier_root_namecert_ledger_exactness [AskSetup] [PackageSetup]
    {A B C f g u H K L N category generator ledger : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ContinuationMonadCarrier A B C f g u H K L N →
      Cont L N category →
        Cont category N generator →
          Cont generator N ledger →
            PkgSig bundle ledger pkg →
              SemanticNameCert
                (fun row : BHist =>
                  ContinuationMonadCarrier A B C f g u H K L N ∧
                    Cont L N category ∧ Cont category N generator ∧
                      Cont generator N ledger ∧ hsame row ledger)
                (fun row : BHist =>
                  Cont A f B ∧ Cont B g C ∧ Cont f g K ∧ Cont K u L ∧
                    Cont L N category ∧ Cont category N generator ∧
                      Cont generator N ledger ∧ hsame row ledger)
                (fun row : BHist => UnaryHistory row ∧ hsame N L ∧ PkgSig bundle ledger pkg)
                hsame := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont SemanticNameCert hsame
  intro carrier categoryRoute generatorRoute ledgerRoute ledgerPkg
  obtain ⟨unaryA, unaryF, unaryG, unaryU, routeB, routeC, routeK, routeL,
    sameEndpoint⟩ := carrier
  have unaryK : UnaryHistory K :=
    unary_cont_closed unaryF unaryG routeK
  have unaryL : UnaryHistory L :=
    unary_cont_closed unaryK unaryU routeL
  have unaryN : UnaryHistory N :=
    unary_transport unaryL (hsame_symm sameEndpoint)
  have unaryCategory : UnaryHistory category :=
    unary_cont_closed unaryL unaryN categoryRoute
  have unaryGenerator : UnaryHistory generator :=
    unary_cont_closed unaryCategory unaryN generatorRoute
  have unaryLedger : UnaryHistory ledger :=
    unary_cont_closed unaryGenerator unaryN ledgerRoute
  have carrierSource : ContinuationMonadCarrier A B C f g u H K L N :=
    ⟨unaryA, unaryF, unaryG, unaryU, routeB, routeC, routeK, routeL, sameEndpoint⟩
  exact {
    core := {
      carrier_inhabited :=
        Exists.intro ledger
          ⟨carrierSource, categoryRoute, generatorRoute, ledgerRoute, hsame_refl ledger⟩
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
            source.right.right.right.left,
            hsame_trans (hsame_symm same) source.right.right.right.right⟩
    }
    pattern_sound := by
      intro _row source
      exact
        ⟨routeB, routeC, routeK, routeL, source.right.left,
          source.right.right.left, source.right.right.right.left,
          source.right.right.right.right⟩
    ledger_sound := by
      intro _row source
      exact
        ⟨unary_transport unaryLedger (hsame_symm source.right.right.right.right),
          sameEndpoint, ledgerPkg⟩
  }

end BEDC.Derived.ContinuationMonadUp
