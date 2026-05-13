import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.CauchyModulusMeetUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def CauchyModulusMeetPacket [AskSetup] [PackageSetup]
    (s0 s1 mu0 mu1 mu h c p n : BHist) (bundle : ProbeBundle ProbeName) (pkg : Pkg) :
    Prop :=
  UnaryHistory s0 ∧ UnaryHistory s1 ∧ UnaryHistory mu0 ∧ UnaryHistory mu1 ∧
    UnaryHistory mu ∧ UnaryHistory h ∧ UnaryHistory c ∧ UnaryHistory p ∧ UnaryHistory n ∧
      Cont s0 mu0 h ∧ Cont s1 mu1 c ∧ Cont h c mu ∧ hsame p n ∧
        PkgSig bundle p pkg

theorem CauchyModulusMeetPacket_namecert_obligations [AskSetup] [PackageSetup]
    {s0 s1 mu0 mu1 mu h c p n : BHist} {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CauchyModulusMeetPacket s0 s1 mu0 mu1 mu h c p n bundle pkg →
      SemanticNameCert
        (fun row : BHist =>
          CauchyModulusMeetPacket s0 s1 mu0 mu1 mu h c p n bundle pkg ∧ hsame row mu)
        (fun row : BHist => Cont s0 mu0 h ∧ Cont s1 mu1 c ∧ Cont h c row ∧
          PkgSig bundle p pkg)
        (fun _row : BHist =>
          UnaryHistory s0 ∧ UnaryHistory s1 ∧ UnaryHistory mu0 ∧ UnaryHistory mu1 ∧
            UnaryHistory mu ∧ UnaryHistory h ∧ UnaryHistory c ∧ UnaryHistory p ∧
              UnaryHistory n)
        hsame := by
  -- BEDC touchpoint anchor: BHist Cont hsame ProbeBundle Pkg NameCert
  intro packet
  have packetWitness := packet
  obtain ⟨s0Unary, s1Unary, mu0Unary, mu1Unary, muUnary, hUnary, cUnary, pUnary,
    nUnary, hRow, cRow, muRow, _samePN, endpointPkg⟩ := packet
  constructor
  · constructor
    · exact Exists.intro mu ⟨packetWitness, hsame_refl mu⟩
    · intro row _source
      exact hsame_refl row
    · intro _row _other same
      exact hsame_symm same
    · intro _row _other _third sameLeft sameRight
      exact hsame_trans sameLeft sameRight
    · intro _row _other same source
      exact ⟨source.left, hsame_trans (hsame_symm same) source.right⟩
  · intro _row source
    cases source.right
    exact ⟨hRow, cRow, muRow, endpointPkg⟩
  · intro _row _source
    exact ⟨s0Unary, s1Unary, mu0Unary, mu1Unary, muUnary, hUnary, cUnary, pUnary, nUnary⟩

theorem CauchyModulusMeetPacket_projection_stability [AskSetup] [PackageSetup]
    {s0 s1 mu0 mu1 mu h c p n s0' s1' mu0' mu1' mu' h' c' p' n' : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CauchyModulusMeetPacket s0 s1 mu0 mu1 mu h c p n bundle pkg ->
      hsame s0 s0' -> hsame s1 s1' -> hsame mu0 mu0' -> hsame mu1 mu1' ->
        hsame mu mu' -> hsame p p' -> hsame n n' -> Cont s0' mu0' h' ->
          Cont s1' mu1' c' -> Cont h' c' mu' -> PkgSig bundle p' pkg ->
            CauchyModulusMeetPacket s0' s1' mu0' mu1' mu' h' c' p' n' bundle pkg ∧
              hsame mu mu' := by
  intro packet sameS0 sameS1 sameMu0 sameMu1 sameMu sameP sameN hRow' cRow' muRow' pkg'
  have hRow : Cont s0 mu0 h :=
    packet.right.right.right.right.right.right.right.right.right.left
  have cRow : Cont s1 mu1 c :=
    packet.right.right.right.right.right.right.right.right.right.right.left
  have muRow : Cont h c mu :=
    packet.right.right.right.right.right.right.right.right.right.right.right.left
  have hsameH : hsame h h' :=
    cont_respects_hsame sameS0 sameMu0 hRow hRow'
  have hsameC : hsame c c' :=
    cont_respects_hsame sameS1 sameMu1 cRow cRow'
  have hsameMuFromRoutes : hsame mu mu' :=
    cont_respects_hsame hsameH hsameC muRow muRow'
  have s0Unary' : UnaryHistory s0' :=
    unary_transport packet.left sameS0
  have s1Unary' : UnaryHistory s1' :=
    unary_transport packet.right.left sameS1
  have mu0Unary' : UnaryHistory mu0' :=
    unary_transport packet.right.right.left sameMu0
  have mu1Unary' : UnaryHistory mu1' :=
    unary_transport packet.right.right.right.left sameMu1
  have muUnary' : UnaryHistory mu' :=
    unary_transport packet.right.right.right.right.left sameMu
  have hUnary' : UnaryHistory h' :=
    unary_transport packet.right.right.right.right.right.left hsameH
  have cUnary' : UnaryHistory c' :=
    unary_transport packet.right.right.right.right.right.right.left hsameC
  have pUnary' : UnaryHistory p' :=
    unary_transport packet.right.right.right.right.right.right.right.left sameP
  have nUnary' : UnaryHistory n' :=
    unary_transport packet.right.right.right.right.right.right.right.right.left sameN
  have samePN' : hsame p' n' :=
    hsame_trans (hsame_symm sameP)
      (hsame_trans packet.right.right.right.right.right.right.right.right.right.right.right.right.left
        sameN)
  exact
    ⟨⟨s0Unary',
      s1Unary',
      mu0Unary',
      mu1Unary',
      muUnary',
      hUnary',
      cUnary',
      pUnary',
      nUnary',
      hRow',
      cRow',
      muRow',
      samePN',
      pkg'⟩,
      hsameMuFromRoutes⟩

theorem CauchyModulusMeetPacket_shared_bound_transport [AskSetup] [PackageSetup]
    {s0 s1 mu0 mu1 mu h c p n s0' s1' mu0' mu1' h' c' mu' : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CauchyModulusMeetPacket s0 s1 mu0 mu1 mu h c p n bundle pkg ->
      hsame s0 s0' -> hsame s1 s1' -> hsame mu0 mu0' -> hsame mu1 mu1' ->
        Cont s0' mu0' h' -> Cont s1' mu1' c' -> Cont h' c' mu' ->
          UnaryHistory mu' ∧ hsame mu mu' := by
  intro packet sameS0 sameS1 sameMu0 sameMu1 hRow' cRow' muRow'
  have hRow : Cont s0 mu0 h :=
    packet.right.right.right.right.right.right.right.right.right.left
  have cRow : Cont s1 mu1 c :=
    packet.right.right.right.right.right.right.right.right.right.right.left
  have muRow : Cont h c mu :=
    packet.right.right.right.right.right.right.right.right.right.right.right.left
  have sameH : hsame h h' :=
    cont_respects_hsame sameS0 sameMu0 hRow hRow'
  have sameC : hsame c c' :=
    cont_respects_hsame sameS1 sameMu1 cRow cRow'
  have sameMu : hsame mu mu' :=
    cont_respects_hsame sameH sameC muRow muRow'
  exact ⟨unary_transport packet.right.right.right.right.left sameMu, sameMu⟩

theorem CauchyModulusMeetPacket_swap_stability [AskSetup] [PackageSetup]
    {s0 s1 mu0 mu1 mu h c p n hSw cSw : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CauchyModulusMeetPacket s0 s1 mu0 mu1 mu h c p n bundle pkg ->
      Cont s1 mu1 hSw -> Cont s0 mu0 cSw -> Cont hSw cSw mu ->
        CauchyModulusMeetPacket s1 s0 mu1 mu0 mu hSw cSw p n bundle pkg ∧
          hsame mu mu := by
  intro packet hRowSw cRowSw muRowSw
  have s0Unary : UnaryHistory s0 := packet.left
  have s1Unary : UnaryHistory s1 := packet.right.left
  have mu0Unary : UnaryHistory mu0 := packet.right.right.left
  have mu1Unary : UnaryHistory mu1 := packet.right.right.right.left
  have muUnary : UnaryHistory mu := packet.right.right.right.right.left
  have pUnary : UnaryHistory p :=
    packet.right.right.right.right.right.right.right.left
  have nUnary : UnaryHistory n :=
    packet.right.right.right.right.right.right.right.right.left
  have hUnarySw : UnaryHistory hSw :=
    unary_cont_closed s1Unary mu1Unary hRowSw
  have cUnarySw : UnaryHistory cSw :=
    unary_cont_closed s0Unary mu0Unary cRowSw
  exact
    ⟨⟨s1Unary,
      s0Unary,
      mu1Unary,
      mu0Unary,
      muUnary,
      hUnarySw,
      cUnarySw,
      pUnary,
      nUnary,
      hRowSw,
      cRowSw,
      muRowSw,
      packet.right.right.right.right.right.right.right.right.right.right.right.right.left,
      packet.right.right.right.right.right.right.right.right.right.right.right.right.right⟩,
      hsame_refl mu⟩

theorem CauchyModulusMeetPacket_real_handoff_boundary [AskSetup] [PackageSetup]
    {s0 s1 mu0 mu1 mu h c p n realRoute handoff : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CauchyModulusMeetPacket s0 s1 mu0 mu1 mu h c p n bundle pkg ->
      Cont mu n realRoute -> Cont realRoute p handoff ->
        UnaryHistory realRoute /\ UnaryHistory handoff /\ hsame p n /\ PkgSig bundle p pkg := by
  -- BEDC touchpoint anchor: BHist Cont hsame ProbeBundle Pkg
  intro packet realRouteRow handoffRow
  have realRouteUnary : UnaryHistory realRoute :=
    unary_cont_closed packet.right.right.right.right.left
      packet.right.right.right.right.right.right.right.right.left realRouteRow
  have handoffUnary : UnaryHistory handoff :=
    unary_cont_closed realRouteUnary packet.right.right.right.right.right.right.right.left
      handoffRow
  exact
    ⟨realRouteUnary,
      handoffUnary,
      packet.right.right.right.right.right.right.right.right.right.right.right.right.left,
      packet.right.right.right.right.right.right.right.right.right.right.right.right.right⟩

theorem CauchyModulusMeetPacket_consumer_factorization [AskSetup] [PackageSetup]
    {s0 s1 mu0 mu1 mu h c p n realRoute handoff : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CauchyModulusMeetPacket s0 s1 mu0 mu1 mu h c p n bundle pkg →
      Cont mu n realRoute →
        Cont realRoute p handoff →
          UnaryHistory s0 ∧ UnaryHistory s1 ∧ UnaryHistory mu0 ∧ UnaryHistory mu1 ∧
            UnaryHistory mu ∧ UnaryHistory realRoute ∧ UnaryHistory handoff ∧
              Cont s0 mu0 h ∧ Cont s1 mu1 c ∧ Cont h c mu ∧
                Cont mu n realRoute ∧ Cont realRoute p handoff ∧ PkgSig bundle p pkg := by
  intro packet realRouteRow handoffRow
  obtain ⟨s0Unary, s1Unary, mu0Unary, mu1Unary, muUnary, _hUnary, _cUnary, pUnary,
    nUnary, s0Mu0H, s1Mu1C, hCMu, _samePN, pPkg⟩ := packet
  have realRouteUnary : UnaryHistory realRoute :=
    unary_cont_closed muUnary nUnary realRouteRow
  have handoffUnary : UnaryHistory handoff :=
    unary_cont_closed realRouteUnary pUnary handoffRow
  exact
    ⟨s0Unary, s1Unary, mu0Unary, mu1Unary, muUnary, realRouteUnary, handoffUnary,
      s0Mu0H, s1Mu1C, hCMu, realRouteRow, handoffRow, pPkg⟩

end BEDC.Derived.CauchyModulusMeetUp
