import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.ContinuationMonadUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def ContinuationMonadCarrier (A B C f g u _H K L N : BHist) : Prop :=
  UnaryHistory A ∧ UnaryHistory f ∧ UnaryHistory g ∧ UnaryHistory u ∧
    Cont A f B ∧ Cont B g C ∧ Cont f g K ∧ Cont K u L ∧ hsame N L

theorem ContinuationMonadCarrier_route_closure {A B C f g u H K L N : BHist} :
    ContinuationMonadCarrier A B C f g u H K L N ->
      UnaryHistory B ∧ UnaryHistory C ∧ UnaryHistory K ∧ UnaryHistory L ∧ hsame N L := by
  intro packet
  have unaryA : UnaryHistory A :=
    packet.left
  have unaryF : UnaryHistory f :=
    packet.right.left
  have unaryG : UnaryHistory g :=
    packet.right.right.left
  have unaryU : UnaryHistory u :=
    packet.right.right.right.left
  have routeB : Cont A f B :=
    packet.right.right.right.right.left
  have routeC : Cont B g C :=
    packet.right.right.right.right.right.left
  have routeK : Cont f g K :=
    packet.right.right.right.right.right.right.left
  have routeL : Cont K u L :=
    packet.right.right.right.right.right.right.right.left
  have sameEndpoint : hsame N L :=
    packet.right.right.right.right.right.right.right.right
  have unaryB : UnaryHistory B :=
    unary_cont_closed unaryA unaryF routeB
  have unaryC : UnaryHistory C :=
    unary_cont_closed unaryB unaryG routeC
  have unaryK : UnaryHistory K :=
    unary_cont_closed unaryF unaryG routeK
  have unaryL : UnaryHistory L :=
    unary_cont_closed unaryK unaryU routeL
  exact ⟨unaryB, unaryC, unaryK, unaryL, sameEndpoint⟩

theorem ContinuationMonadCarrier_kleisli_associativity_surface
    {A B C f g u H K L N read : BHist} :
    ContinuationMonadCarrier A B C f g u H K L N ->
      Cont L N read ->
        UnaryHistory B ∧ UnaryHistory C ∧ UnaryHistory K ∧ UnaryHistory L ∧
          UnaryHistory read ∧ hsame N L ∧ Cont L N read := by
  intro carrier routeRead
  have closure :
      UnaryHistory B ∧ UnaryHistory C ∧ UnaryHistory K ∧ UnaryHistory L ∧ hsame N L :=
    ContinuationMonadCarrier_route_closure carrier
  have unaryL : UnaryHistory L :=
    closure.right.right.right.left
  have sameEndpoint : hsame N L :=
    closure.right.right.right.right
  have unaryN : UnaryHistory N := by
    cases sameEndpoint
    exact unaryL
  have unaryRead : UnaryHistory read :=
    unary_cont_closed unaryL unaryN routeRead
  exact
    ⟨closure.left, closure.right.left, closure.right.right.left, unaryL, unaryRead,
      sameEndpoint, routeRead⟩

theorem ContinuationMonadCarrier_root_kleisli_associativity_surface
    [AskSetup] [PackageSetup]
    {A B C f g u H K L N : BHist} {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ContinuationMonadCarrier A B C f g u H K L N ->
      PkgSig bundle L pkg ->
        UnaryHistory A ∧ UnaryHistory B ∧ UnaryHistory C ∧ UnaryHistory K ∧
          UnaryHistory L ∧ Cont A f B ∧ Cont B g C ∧ Cont f g K ∧
            Cont K u L ∧ hsame N L ∧
              SemanticNameCert
                (fun row : BHist => hsame row L ∧ UnaryHistory row)
                (fun row : BHist => hsame row L)
                (fun row : BHist => hsame row L ∧ PkgSig bundle L pkg)
                hsame := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont SemanticNameCert hsame
  intro carrier pkgSig
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
  have sourceL : (fun row : BHist => hsame row L ∧ UnaryHistory row) L := by
    exact And.intro (hsame_refl L) unaryL
  have cert :
      SemanticNameCert
        (fun row : BHist => hsame row L ∧ UnaryHistory row)
        (fun row : BHist => hsame row L)
        (fun row : BHist => hsame row L ∧ PkgSig bundle L pkg)
        hsame := by
    exact {
      core := {
        carrier_inhabited := Exists.intro L sourceL
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
          intro row other same source
          exact And.intro (hsame_trans (hsame_symm same) source.left)
            (unary_transport source.right same)
      }
      pattern_sound := by
        intro _row source
        exact source.left
      ledger_sound := by
        intro _row source
        exact And.intro source.left pkgSig
    }
  exact
    ⟨unaryA, unaryB, unaryC, unaryK, unaryL, routeB, routeC, routeK, routeL,
      sameEndpoint, cert⟩

theorem ContinuationMonadCarrier_root_route_source_exposure {A B C f g u H K L N : BHist}
    (packet : ContinuationMonadCarrier A B C f g u H K L N) :
    UnaryHistory A ∧ UnaryHistory B ∧ UnaryHistory C ∧ UnaryHistory f ∧ UnaryHistory g ∧
      UnaryHistory u ∧ Cont A f B ∧ Cont B g C ∧ Cont f g K ∧ Cont K u L ∧
        UnaryHistory K ∧ UnaryHistory L ∧ hsame N L := by
  -- BEDC touchpoint anchor: BHist Cont
  have unaryA : UnaryHistory A :=
    packet.left
  have unaryF : UnaryHistory f :=
    packet.right.left
  have unaryG : UnaryHistory g :=
    packet.right.right.left
  have unaryU : UnaryHistory u :=
    packet.right.right.right.left
  have routeB : Cont A f B :=
    packet.right.right.right.right.left
  have routeC : Cont B g C :=
    packet.right.right.right.right.right.left
  have routeK : Cont f g K :=
    packet.right.right.right.right.right.right.left
  have routeL : Cont K u L :=
    packet.right.right.right.right.right.right.right.left
  have sameEndpoint : hsame N L :=
    packet.right.right.right.right.right.right.right.right
  have unaryB : UnaryHistory B :=
    unary_cont_closed unaryA unaryF routeB
  have unaryC : UnaryHistory C :=
    unary_cont_closed unaryB unaryG routeC
  have unaryK : UnaryHistory K :=
    unary_cont_closed unaryF unaryG routeK
  have unaryL : UnaryHistory L :=
    unary_cont_closed unaryK unaryU routeL
  exact
    ⟨unaryA, unaryB, unaryC, unaryF, unaryG, unaryU, routeB, routeC, routeK, routeL,
      unaryK, unaryL, sameEndpoint⟩

theorem ContinuationMonadCarrier_root_downstream_readback_package
    [AskSetup] [PackageSetup]
    {A B C f g u H K L N : BHist} {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ContinuationMonadCarrier A B C f g u H K L N ->
      PkgSig bundle L pkg ->
        UnaryHistory A ∧ UnaryHistory B ∧ UnaryHistory C ∧ UnaryHistory f ∧
          UnaryHistory g ∧ UnaryHistory u ∧ Cont A f B ∧ Cont B g C ∧ Cont f g K ∧
            Cont K u L ∧ UnaryHistory K ∧ UnaryHistory L ∧ hsame N L ∧
              SemanticNameCert
                (fun row : BHist => hsame row L ∧ UnaryHistory row)
                (fun row : BHist => hsame row L)
                (fun row : BHist => hsame row L ∧ PkgSig bundle L pkg)
                hsame := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont SemanticNameCert hsame
  intro carrier pkgSig
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
  have sourceL : (fun row : BHist => hsame row L ∧ UnaryHistory row) L := by
    exact And.intro (hsame_refl L) unaryL
  have cert :
      SemanticNameCert
        (fun row : BHist => hsame row L ∧ UnaryHistory row)
        (fun row : BHist => hsame row L)
        (fun row : BHist => hsame row L ∧ PkgSig bundle L pkg)
        hsame := by
    exact {
      core := {
        carrier_inhabited := Exists.intro L sourceL
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
          intro row other same source
          exact And.intro (hsame_trans (hsame_symm same) source.left)
            (unary_transport source.right same)
      }
      pattern_sound := by
        intro _row source
        exact source.left
      ledger_sound := by
        intro _row source
        exact And.intro source.left pkgSig
    }
  exact
    ⟨unaryA, unaryB, unaryC, unaryF, unaryG, unaryU, routeB, routeC, routeK, routeL,
      unaryK, unaryL, sameEndpoint, cert⟩

theorem ContinuationMonadCarrier_root_downstream_consumer_separation
    [AskSetup] [PackageSetup]
    {A B C f g u H K L N consumer : BHist} {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ContinuationMonadCarrier A B C f g u H K L N ->
      Cont L N consumer ->
        PkgSig bundle consumer pkg ->
          UnaryHistory A ∧ UnaryHistory B ∧ UnaryHistory C ∧ UnaryHistory f ∧
            UnaryHistory g ∧ UnaryHistory u ∧ UnaryHistory K ∧ UnaryHistory L ∧
              UnaryHistory consumer ∧ Cont A f B ∧ Cont B g C ∧ Cont f g K ∧
                Cont K u L ∧ Cont L N consumer ∧ hsame N L ∧
                  PkgSig bundle consumer pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont UnaryHistory hsame
  intro carrier consumerRoute consumerPkg
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
  have consumerUnary : UnaryHistory consumer :=
    unary_cont_closed unaryL unaryN consumerRoute
  exact
    ⟨unaryA, unaryB, unaryC, unaryF, unaryG, unaryU, unaryK, unaryL, consumerUnary,
      routeB, routeC, routeK, routeL, consumerRoute, sameEndpoint, consumerPkg⟩

theorem ContinuationMonadCarrier_root_continuation_rule_coverage
    [AskSetup] [PackageSetup]
    {A B C f g u H K L N : BHist} {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ContinuationMonadCarrier A B C f g u H K L N ->
      PkgSig bundle L pkg ->
        SemanticNameCert
          (fun row : BHist =>
            ContinuationMonadCarrier A B C f g u H K L N ∧ hsame row L)
          (fun row : BHist =>
            Cont f g K ∧ Cont K u L ∧ hsame row L ∧ PkgSig bundle L pkg)
          (fun row : BHist => UnaryHistory row ∧ hsame N L ∧ PkgSig bundle L pkg)
          hsame := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont SemanticNameCert hsame
  intro carrier pkgSig
  obtain ⟨unaryA, unaryF, unaryG, unaryU, routeB, routeC, routeK, routeL,
    sameEndpoint⟩ := carrier
  have unaryK : UnaryHistory K :=
    unary_cont_closed unaryF unaryG routeK
  have unaryL : UnaryHistory L :=
    unary_cont_closed unaryK unaryU routeL
  exact {
    core := {
      carrier_inhabited :=
        Exists.intro L
          (And.intro
            ⟨unaryA, unaryF, unaryG, unaryU, routeB, routeC, routeK, routeL,
              sameEndpoint⟩
            (hsame_refl L))
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
        intro row other same source
        exact And.intro source.left (hsame_trans (hsame_symm same) source.right)
    }
    pattern_sound := by
      intro _row source
      exact ⟨routeK, routeL, source.right, pkgSig⟩
    ledger_sound := by
      intro _row source
      exact ⟨unary_transport unaryL (hsame_symm source.right), sameEndpoint, pkgSig⟩
  }

theorem ContinuationMonadCarrier_root_ledger_formal_boundary
    [AskSetup] [PackageSetup]
    {A B C f g u H K L N ledgerRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ContinuationMonadCarrier A B C f g u H K L N ->
      Cont L N ledgerRead ->
        PkgSig bundle ledgerRead pkg ->
          UnaryHistory A ∧ UnaryHistory B ∧ UnaryHistory C ∧ UnaryHistory f ∧
            UnaryHistory g ∧ UnaryHistory u ∧ UnaryHistory K ∧ UnaryHistory L ∧
              UnaryHistory N ∧ UnaryHistory ledgerRead ∧ Cont A f B ∧ Cont B g C ∧
                Cont f g K ∧ Cont K u L ∧ Cont L N ledgerRead ∧ hsame N L ∧
                  PkgSig bundle ledgerRead pkg ∧
                    SemanticNameCert
                      (fun row : BHist => hsame row ledgerRead ∧ UnaryHistory row)
                      (fun row : BHist => hsame row ledgerRead)
                      (fun row : BHist => hsame row ledgerRead ∧ PkgSig bundle ledgerRead pkg)
                      hsame := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont SemanticNameCert hsame
  intro carrier ledgerRoute ledgerPkg
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
  have ledgerUnary : UnaryHistory ledgerRead :=
    unary_cont_closed unaryL unaryN ledgerRoute
  have cert :
      SemanticNameCert
        (fun row : BHist => hsame row ledgerRead ∧ UnaryHistory row)
        (fun row : BHist => hsame row ledgerRead)
        (fun row : BHist => hsame row ledgerRead ∧ PkgSig bundle ledgerRead pkg)
        hsame := by
    exact {
      core := {
        carrier_inhabited :=
          Exists.intro ledgerRead (And.intro (hsame_refl ledgerRead) ledgerUnary)
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
        exact And.intro source.left ledgerPkg
    }
  exact
    ⟨unaryA, unaryB, unaryC, unaryF, unaryG, unaryU, unaryK, unaryL, unaryN,
      ledgerUnary, routeB, routeC, routeK, routeL, ledgerRoute, sameEndpoint, ledgerPkg,
      cert⟩

end BEDC.Derived.ContinuationMonadUp
