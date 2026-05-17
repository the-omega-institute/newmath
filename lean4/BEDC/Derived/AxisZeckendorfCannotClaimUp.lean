import BEDC.Derived.AxisZeckendorf
import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.AxisZeckendorfCannotClaimUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def AxisZeckendorfCannotClaimRegistryPacket [AskSetup] [PackageSetup]
    (a b c d e f g h p n : BHist) (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  UnaryHistory a ∧
    UnaryHistory b ∧
      UnaryHistory c ∧
        UnaryHistory d ∧
          UnaryHistory e ∧
            UnaryHistory f ∧
              UnaryHistory g ∧
                Cont a b h ∧
                  Cont c d h ∧
                    Cont e f h ∧ UnaryHistory p ∧ hsame p n ∧ PkgSig bundle p pkg

theorem AxisZeckendorfCannotClaimRegistryPacket_source_row_coverage [AskSetup] [PackageSetup]
    {a b c d e f g h p n : BHist} {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    AxisZeckendorfCannotClaimRegistryPacket a b c d e f g h p n bundle pkg ->
      UnaryHistory a ∧ UnaryHistory b ∧ UnaryHistory c ∧ UnaryHistory d ∧
        UnaryHistory e ∧ UnaryHistory f ∧ UnaryHistory g ∧ Cont a b h ∧ Cont c d h ∧
          Cont e f h ∧ UnaryHistory p ∧ hsame p n ∧ PkgSig bundle p pkg := by
  intro packet
  obtain
    ⟨aUnary, bUnary, cUnary, dUnary, eUnary, fUnary, gUnary, routeAB, routeCD, routeEF,
      pUnary, sameProvenanceName, pkgSig⟩ := packet
  exact
    ⟨aUnary, bUnary, cUnary, dUnary, eUnary, fUnary, gUnary, routeAB, routeCD, routeEF,
      pUnary, sameProvenanceName, pkgSig⟩

theorem AxisZeckendorfCannotClaimRegistryPacket_transport_nonpromotion [AskSetup] [PackageSetup]
    {a b c d e f g h p n a' b' c' d' e' f' g' h' p' n' : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    AxisZeckendorfCannotClaimRegistryPacket a b c d e f g h p n bundle pkg ->
      hsame a a' ->
        hsame b b' ->
          hsame c c' ->
            hsame d d' ->
              hsame e e' ->
                hsame f f' ->
                  hsame g g' ->
                    hsame p p' ->
                      hsame n n' ->
                        Cont a' b' h' ->
                          Cont c' d' h' ->
                            Cont e' f' h' ->
                              PkgSig bundle p' pkg ->
                                AxisZeckendorfCannotClaimRegistryPacket a' b' c' d' e' f'
                                    g' h' p' n' bundle pkg ∧
                                  hsame h h' ∧ hsame p' n' := by
  intro packet sameA sameB sameC sameD sameE sameF sameG sameP sameN routeAB' routeCD'
    routeEF' pkgSig'
  obtain
    ⟨aUnary, bUnary, cUnary, dUnary, eUnary, fUnary, gUnary, routeAB, _routeCD, _routeEF,
      pUnary, sameProvenanceName, _pkgSig⟩ := packet
  have routeSame : hsame h h' := cont_respects_hsame sameA sameB routeAB routeAB'
  have transportedProvenanceName : hsame p' n' :=
    hsame_trans (hsame_symm sameP) (hsame_trans sameProvenanceName sameN)
  constructor
  · exact
      ⟨unary_transport aUnary sameA, unary_transport bUnary sameB,
        unary_transport cUnary sameC, unary_transport dUnary sameD,
        unary_transport eUnary sameE, unary_transport fUnary sameF,
        unary_transport gUnary sameG, routeAB', routeCD', routeEF',
        unary_transport pUnary sameP, transportedProvenanceName, pkgSig'⟩
  · exact ⟨routeSame, transportedProvenanceName⟩

theorem AxisZeckendorfCannotClaimRegistryPacket_semantic_name_certificate [AskSetup]
    [PackageSetup] {a b c d e f g h p n : BHist} {bundle : ProbeBundle ProbeName}
    {pkg : Pkg} :
    AxisZeckendorfCannotClaimRegistryPacket a b c d e f g h p n bundle pkg ->
      SemanticNameCert
        (fun row : BHist =>
          AxisZeckendorfCannotClaimRegistryPacket a b c d e f g h p n bundle pkg ∧
            hsame row n)
        (fun row : BHist =>
          AxisZeckendorfCannotClaimRegistryPacket a b c d e f g h p n bundle pkg ∧
            hsame row n)
        (fun row : BHist =>
          AxisZeckendorfCannotClaimRegistryPacket a b c d e f g h p n bundle pkg ∧
            hsame row n)
        hsame := by
  -- BEDC touchpoint anchor: BHist UnaryHistory Cont PkgSig hsame SemanticNameCert
  intro packet
  have packetWitness :
      AxisZeckendorfCannotClaimRegistryPacket a b c d e f g h p n bundle pkg := packet
  exact {
    core := {
      carrier_inhabited := Exists.intro n ⟨packetWitness, hsame_refl n⟩
      equiv_refl := by
        intro row _source
        exact hsame_refl row
      equiv_symm := by
        intro _row _row' sameRows
        exact hsame_symm sameRows
      equiv_trans := by
        intro _row _row' _row'' sameLeft sameRight
        exact hsame_trans sameLeft sameRight
      carrier_respects_equiv := by
        intro _row _row' sameRows source
        exact ⟨source.left, hsame_trans (hsame_symm sameRows) source.right⟩
    }
    pattern_sound := by
      intro _row source
      exact source
    ledger_sound := by
      intro _row source
      exact source
  }

theorem AxisZeckendorfCannotClaimRegistryPacket_ledger_exactness [AskSetup]
    [PackageSetup] {a b c d e f g h p n : BHist} {bundle : ProbeBundle ProbeName}
    {pkg : Pkg} :
    AxisZeckendorfCannotClaimRegistryPacket a b c d e f g h p n bundle pkg ->
      hsame p n ∧
        PkgSig bundle p pkg ∧
          SemanticNameCert
            (fun row : BHist => hsame row p ∧ hsame p n)
            (fun row : BHist => PkgSig bundle p pkg ∧ hsame row n)
            (fun row : BHist =>
              AxisZeckendorfCannotClaimRegistryPacket a b c d e f g h p n bundle pkg ∧
                hsame row n)
            hsame := by
  -- BEDC touchpoint anchor: BHist hsame PkgSig SemanticNameCert
  intro packet
  have packetWitness :
      AxisZeckendorfCannotClaimRegistryPacket a b c d e f g h p n bundle pkg := packet
  obtain
    ⟨_aUnary, _bUnary, _cUnary, _dUnary, _eUnary, _fUnary, _gUnary, _routeAB,
      _routeCD, _routeEF, _pUnary, sameProvenanceName, pkgSig⟩ := packet
  constructor
  · exact sameProvenanceName
  · constructor
    · exact pkgSig
    · exact {
        core := {
          carrier_inhabited := Exists.intro p ⟨hsame_refl p, sameProvenanceName⟩
          equiv_refl := by
            intro row _source
            exact hsame_refl row
          equiv_symm := by
            intro _row _row' sameRows
            exact hsame_symm sameRows
          equiv_trans := by
            intro _row _row' _row'' sameLeft sameRight
            exact hsame_trans sameLeft sameRight
          carrier_respects_equiv := by
            intro _row _row' sameRows source
            exact ⟨hsame_trans (hsame_symm sameRows) source.left, source.right⟩
        }
        pattern_sound := by
          intro _row source
          exact ⟨pkgSig, hsame_trans source.left sameProvenanceName⟩
        ledger_sound := by
          intro _row source
          exact ⟨packetWitness, hsame_trans source.left sameProvenanceName⟩
      }

theorem AxisZeckendorfCannotClaimRegistryPacket_root_unblock_downstream_boundary [AskSetup]
    [PackageSetup] {a b c d e f g h p n downstream : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    AxisZeckendorfCannotClaimRegistryPacket a b c d e f g h p n bundle pkg ->
      Cont a b downstream ->
        hsame h downstream ∧ hsame p n ∧ PkgSig bundle p pkg := by
  -- BEDC touchpoint anchor: BHist hsame Cont ProbeBundle Pkg PkgSig
  intro packet downstreamRoute
  obtain
    ⟨_aUnary, _bUnary, _cUnary, _dUnary, _eUnary, _fUnary, _gUnary, rootRoute, _routeCD,
      _routeEF, _pUnary, sameProvenanceName, pkgSig⟩ := packet
  have sameRootDownstream : hsame h downstream :=
    cont_deterministic rootRoute downstreamRoute
  exact ⟨sameRootDownstream, sameProvenanceName, pkgSig⟩

theorem AxisZeckendorfCannotClaimRegistryPacket_public_boundary [AskSetup] [PackageSetup]
    {a b c d e f g h p n publicRead : BHist} {bundle : ProbeBundle ProbeName}
    {pkg : Pkg} :
    AxisZeckendorfCannotClaimRegistryPacket a b c d e f g h p n bundle pkg →
      Cont h p publicRead →
        PkgSig bundle publicRead pkg →
          UnaryHistory a ∧ UnaryHistory b ∧ UnaryHistory c ∧ UnaryHistory d ∧
            UnaryHistory e ∧ UnaryHistory f ∧ UnaryHistory g ∧ UnaryHistory h ∧
              UnaryHistory p ∧ UnaryHistory publicRead ∧ Cont h p publicRead ∧
                hsame p n ∧ PkgSig bundle p pkg ∧ PkgSig bundle publicRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont UnaryHistory hsame
  intro packet hProvenancePublic publicPkg
  obtain
    ⟨aUnary, bUnary, cUnary, dUnary, eUnary, fUnary, gUnary, routeAB, _routeCD, _routeEF,
      pUnary, sameProvenanceName, provenancePkg⟩ := packet
  have hUnary : UnaryHistory h :=
    unary_cont_closed aUnary bUnary routeAB
  have publicUnary : UnaryHistory publicRead :=
    unary_cont_closed hUnary pUnary hProvenancePublic
  exact
    ⟨aUnary, bUnary, cUnary, dUnary, eUnary, fUnary, gUnary, hUnary, pUnary, publicUnary,
      hProvenancePublic, sameProvenanceName, provenancePkg, publicPkg⟩

theorem AxisZeckendorfCannotClaimRegistryPacket_refusal_transport [AskSetup] [PackageSetup]
    {a b c d e f g h p n r : BHist} {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    AxisZeckendorfCannotClaimRegistryPacket a b c d e f g h p n bundle pkg ->
      (hsame r a ∨ hsame r b ∨ hsame r c ∨ hsame r d ∨ hsame r e ∨ hsame r f ∨
          hsame r g) ->
        PkgSig bundle r pkg ->
          UnaryHistory r ∧ Cont a b h ∧ Cont c d h ∧ Cont e f h ∧
            (hsame r a ∨ hsame r b ∨ hsame r c ∨ hsame r d ∨ hsame r e ∨
              hsame r f ∨ hsame r g) ∧
              PkgSig bundle r pkg := by
  -- BEDC touchpoint anchor: BHist UnaryHistory Cont PkgSig hsame
  intro packet refusalRow consumerPkg
  obtain
    ⟨aUnary, bUnary, cUnary, dUnary, eUnary, fUnary, gUnary, routeAB, routeCD, routeEF,
      _pUnary, _sameProvenanceName, _pkgSig⟩ := packet
  have consumerUnary : UnaryHistory r := by
    cases refusalRow with
    | inl sameA =>
        exact unary_transport_symm aUnary sameA
    | inr rest =>
        cases rest with
        | inl sameB =>
            exact unary_transport_symm bUnary sameB
        | inr rest =>
            cases rest with
            | inl sameC =>
                exact unary_transport_symm cUnary sameC
            | inr rest =>
                cases rest with
                | inl sameD =>
                    exact unary_transport_symm dUnary sameD
                | inr rest =>
                    cases rest with
                    | inl sameE =>
                        exact unary_transport_symm eUnary sameE
                    | inr rest =>
                        cases rest with
                        | inl sameF =>
                            exact unary_transport_symm fUnary sameF
                        | inr sameG =>
                            exact unary_transport_symm gUnary sameG
  exact ⟨consumerUnary, routeAB, routeCD, routeEF, refusalRow, consumerPkg⟩

theorem AxisZeckendorfCannotClaimRegistryPacket_audit_gate_boundary [AskSetup] [PackageSetup]
    {a b c d e f g h p n r audit : BHist} {bundle : ProbeBundle ProbeName}
    {pkg : Pkg} :
    AxisZeckendorfCannotClaimRegistryPacket a b c d e f g h p n bundle pkg ->
      (hsame r a ∨ hsame r b ∨ hsame r c ∨ hsame r d ∨ hsame r e ∨ hsame r f ∨
          hsame r g) ->
        PkgSig bundle r pkg ->
          Cont h p audit ->
            PkgSig bundle audit pkg ->
              UnaryHistory r ∧ UnaryHistory audit ∧ Cont h p audit ∧ hsame p n ∧
                PkgSig bundle p pkg ∧ PkgSig bundle audit pkg := by
  -- BEDC touchpoint anchor: BHist UnaryHistory Cont PkgSig hsame
  intro packet refusalRow refusalPkg auditRoute auditPkg
  have refusalBoundary :=
    AxisZeckendorfCannotClaimRegistryPacket_refusal_transport packet refusalRow refusalPkg
  have publicBoundary :=
    AxisZeckendorfCannotClaimRegistryPacket_public_boundary packet auditRoute auditPkg
  obtain ⟨refusalUnary, _routeAB, _routeCD, _routeEF, _rowWitness, _rowPkg⟩ :=
    refusalBoundary
  obtain
    ⟨_aUnary, _bUnary, _cUnary, _dUnary, _eUnary, _fUnary, _gUnary, _hUnary,
      _pUnary, auditUnary, auditRoute', sameProvenanceName, provenancePkg,
      auditPkg'⟩ := publicBoundary
  exact
    ⟨refusalUnary, auditUnary, auditRoute', sameProvenanceName, provenancePkg,
      auditPkg'⟩

theorem AxisZeckendorfCannotClaimRegistryPacket_real_refusal_route [AskSetup] [PackageSetup]
    {a b c d e f g h p n e' h' : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    AxisZeckendorfCannotClaimRegistryPacket a b c d e f g h p n bundle pkg ->
      hsame e e' ->
        Cont e' f h' ->
          PkgSig bundle h' pkg ->
            SemanticNameCert
              (fun row : BHist => hsame row h' ∧ UnaryHistory row ∧
                PkgSig bundle row pkg)
              (fun row : BHist => Cont e' f row ∧ UnaryHistory e' ∧ UnaryHistory f)
              (fun row : BHist => PkgSig bundle row pkg ∧ hsame h h')
              (fun row row' : BHist => hsame row row') := by
  -- BEDC touchpoint anchor: BHist UnaryHistory Cont PkgSig hsame SemanticNameCert
  intro packet sameE routeEF' pkgSig'
  obtain
    ⟨_aUnary, _bUnary, _cUnary, _dUnary, eUnary, fUnary, _gUnary, _routeAB,
      _routeCD, routeEF, _pUnary, _sameProvenanceName, _pkgSig⟩ := packet
  have eUnary' : UnaryHistory e' :=
    unary_transport eUnary sameE
  have routeSame : hsame h h' :=
    cont_respects_hsame sameE (hsame_refl f) routeEF routeEF'
  have hUnary' : UnaryHistory h' :=
    unary_cont_closed eUnary' fUnary routeEF'
  exact {
    core := {
      carrier_inhabited := Exists.intro h' ⟨hsame_refl h', hUnary', pkgSig'⟩
      equiv_refl := by
        intro row _source
        exact hsame_refl row
      equiv_symm := by
        intro _row _row' sameRows
        exact hsame_symm sameRows
      equiv_trans := by
        intro _row _row' _row'' sameLeft sameRight
        exact hsame_trans sameLeft sameRight
      carrier_respects_equiv := by
        intro _row _row' sameRows source
        cases sameRows
        exact source
    }
    pattern_sound := by
      intro row source
      exact
        ⟨cont_result_hsame_transport routeEF' (hsame_symm source.left), eUnary',
          fUnary⟩
    ledger_sound := by
      intro _row source
      exact ⟨source.right.right, routeSame⟩
  }

theorem AxisZeckendorfCannotClaimRegistryPacket_nat_refusal_route [AskSetup] [PackageSetup]
    {a b c d e f g h p n fPrime hPrime : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    AxisZeckendorfCannotClaimRegistryPacket a b c d e f g h p n bundle pkg ->
      hsame f fPrime ->
        Cont e fPrime hPrime ->
          PkgSig bundle hPrime pkg ->
            SemanticNameCert
              (fun row : BHist => hsame row hPrime ∧ UnaryHistory row ∧
                PkgSig bundle row pkg)
              (fun row : BHist => Cont e fPrime row ∧ UnaryHistory e ∧ UnaryHistory fPrime)
              (fun row : BHist => PkgSig bundle row pkg ∧ hsame h hPrime)
              (fun row row' : BHist => hsame row row') := by
  -- BEDC touchpoint anchor: BHist UnaryHistory Cont PkgSig hsame SemanticNameCert
  intro packet sameF routeEFPrime pkgSigPrime
  obtain
    ⟨_aUnary, _bUnary, _cUnary, _dUnary, eUnary, fUnary, _gUnary, _routeAB,
      _routeCD, routeEF, _pUnary, _sameProvenanceName, _pkgSig⟩ := packet
  have fPrimeUnary : UnaryHistory fPrime :=
    unary_transport fUnary sameF
  have routeSame : hsame h hPrime :=
    cont_respects_hsame (hsame_refl e) sameF routeEF routeEFPrime
  have hPrimeUnary : UnaryHistory hPrime :=
    unary_cont_closed eUnary fPrimeUnary routeEFPrime
  exact {
    core := {
      carrier_inhabited := Exists.intro hPrime ⟨hsame_refl hPrime, hPrimeUnary, pkgSigPrime⟩
      equiv_refl := by
        intro row _source
        exact hsame_refl row
      equiv_symm := by
        intro _row _row' sameRows
        exact hsame_symm sameRows
      equiv_trans := by
        intro _row _row' _row'' sameLeft sameRight
        exact hsame_trans sameLeft sameRight
      carrier_respects_equiv := by
        intro _row _row' sameRows source
        cases sameRows
        exact source
    }
    pattern_sound := by
      intro row source
      exact
        ⟨cont_result_hsame_transport routeEFPrime (hsame_symm source.left), eUnary,
          fPrimeUnary⟩
    ledger_sound := by
      intro _row source
      exact ⟨source.right.right, routeSame⟩
  }

theorem AxisZeckendorfCannotClaimRegistryPacket_dimlift_refusal_route [AskSetup]
    [PackageSetup] {a b c d e f g h p n gPrime hPrime : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    AxisZeckendorfCannotClaimRegistryPacket a b c d e f g h p n bundle pkg ->
      hsame g gPrime ->
        Cont gPrime h hPrime ->
          PkgSig bundle hPrime pkg ->
            SemanticNameCert
              (fun row : BHist => hsame row hPrime ∧ UnaryHistory row ∧
                PkgSig bundle row pkg)
              (fun row : BHist => Cont gPrime h row ∧ UnaryHistory gPrime ∧ UnaryHistory h)
              (fun row : BHist => PkgSig bundle row pkg ∧ hsame hPrime row)
              (fun row row' : BHist => hsame row row') := by
  -- BEDC touchpoint anchor: BHist UnaryHistory Cont PkgSig hsame SemanticNameCert
  intro packet sameG routeGHPrime pkgSigPrime
  obtain
    ⟨_aUnary, _bUnary, _cUnary, _dUnary, eUnary, fUnary, gUnary, _routeAB,
      _routeCD, routeEF, _pUnary, _sameProvenanceName, _pkgSig⟩ := packet
  have gPrimeUnary : UnaryHistory gPrime :=
    unary_transport gUnary sameG
  have hUnary : UnaryHistory h :=
    unary_cont_closed eUnary fUnary routeEF
  have hPrimeUnary : UnaryHistory hPrime :=
    unary_cont_closed gPrimeUnary hUnary routeGHPrime
  exact {
    core := {
      carrier_inhabited := Exists.intro hPrime ⟨hsame_refl hPrime, hPrimeUnary, pkgSigPrime⟩
      equiv_refl := by
        intro row _source
        exact hsame_refl row
      equiv_symm := by
        intro _row _row' sameRows
        exact hsame_symm sameRows
      equiv_trans := by
        intro _row _row' _row'' sameLeft sameRight
        exact hsame_trans sameLeft sameRight
      carrier_respects_equiv := by
        intro _row _row' sameRows source
        cases sameRows
        exact source
    }
    pattern_sound := by
      intro row source
      exact
        ⟨cont_result_hsame_transport routeGHPrime (hsame_symm source.left),
          gPrimeUnary, hUnary⟩
    ledger_sound := by
      intro _row source
      exact ⟨source.right.right, hsame_symm source.left⟩
  }

theorem AxisZeckendorfCannotClaimRegistryPacket_refusal_ledger_row [AskSetup] [PackageSetup]
    {a b c d e f g h p n refusal : BHist} {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    AxisZeckendorfCannotClaimRegistryPacket a b c d e f g h p n bundle pkg →
      (hsame refusal a ∨ hsame refusal b ∨ hsame refusal c ∨ hsame refusal d ∨
          hsame refusal e ∨ hsame refusal f ∨ hsame refusal g) →
        UnaryHistory refusal ∧ Cont a b h ∧ Cont c d h ∧ Cont e f h ∧ hsame p n ∧
          PkgSig bundle p pkg := by
  -- BEDC touchpoint anchor: BHist UnaryHistory Cont ProbeBundle Pkg PkgSig hsame
  intro packet refusalRow
  obtain
    ⟨aUnary, bUnary, cUnary, dUnary, eUnary, fUnary, gUnary, routeAB, routeCD, routeEF,
      _pUnary, sameProvenanceName, pkgSig⟩ := packet
  have refusalUnary : UnaryHistory refusal := by
    cases refusalRow with
    | inl sameA =>
        exact unary_transport_symm aUnary sameA
    | inr rest =>
        cases rest with
        | inl sameB =>
            exact unary_transport_symm bUnary sameB
        | inr rest =>
            cases rest with
            | inl sameC =>
                exact unary_transport_symm cUnary sameC
            | inr rest =>
                cases rest with
                | inl sameD =>
                    exact unary_transport_symm dUnary sameD
                | inr rest =>
                    cases rest with
                    | inl sameE =>
                        exact unary_transport_symm eUnary sameE
                    | inr rest =>
                        cases rest with
                        | inl sameF =>
                            exact unary_transport_symm fUnary sameF
                        | inr sameG =>
                            exact unary_transport_symm gUnary sameG
  exact ⟨refusalUnary, routeAB, routeCD, routeEF, sameProvenanceName, pkgSig⟩

theorem AxisZeckendorfCannotClaimRegistryPacket_refusal_kernel_scope [AskSetup]
    [PackageSetup] {a b c d e f g h p n refusal transported audit : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    AxisZeckendorfCannotClaimRegistryPacket a b c d e f g h p n bundle pkg ->
      (hsame refusal a ∨ hsame refusal b ∨ hsame refusal c ∨ hsame refusal d ∨
          hsame refusal e ∨ hsame refusal f ∨ hsame refusal g) ->
        hsame refusal transported ->
          Cont h p audit ->
            PkgSig bundle audit pkg ->
              UnaryHistory refusal ∧ UnaryHistory transported ∧ UnaryHistory audit ∧
                Cont a b h ∧ Cont c d h ∧ Cont e f h ∧ Cont h p audit ∧ hsame p n ∧
                  PkgSig bundle p pkg ∧ PkgSig bundle audit pkg := by
  -- BEDC touchpoint anchor: BHist UnaryHistory Cont ProbeBundle Pkg PkgSig hsame
  intro packet refusalRow sameTransported auditRoute auditPkg
  have refusalBoundary :=
    AxisZeckendorfCannotClaimRegistryPacket_refusal_ledger_row packet refusalRow
  have publicBoundary :=
    AxisZeckendorfCannotClaimRegistryPacket_public_boundary packet auditRoute auditPkg
  obtain ⟨refusalUnary, routeAB, routeCD, routeEF, sameProvenanceName, provenancePkg⟩ :=
    refusalBoundary
  obtain
    ⟨_aUnary, _bUnary, _cUnary, _dUnary, _eUnary, _fUnary, _gUnary, _hUnary,
      _pUnary, auditUnary, auditRoute', _sameProvenanceName', _provenancePkg',
      auditPkg'⟩ := publicBoundary
  have transportedUnary : UnaryHistory transported :=
    unary_transport refusalUnary sameTransported
  exact
    ⟨refusalUnary, transportedUnary, auditUnary, routeAB, routeCD, routeEF, auditRoute',
      sameProvenanceName, provenancePkg, auditPkg'⟩

theorem AxisZeckendorfCannotClaimRegistryPacket_positive_bridge_exclusion [AskSetup]
    [PackageSetup] {a b c d e f g h p n bridge : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    AxisZeckendorfCannotClaimRegistryPacket a b c d e f g h p n bundle pkg ->
      Cont h p bridge ->
        PkgSig bundle bridge pkg ->
          SemanticNameCert
            (fun row : BHist =>
              (hsame row h ∨ hsame row p ∨ hsame row n) ∧ UnaryHistory h ∧
                PkgSig bundle p pkg)
            (fun row : BHist =>
              UnaryHistory row ∧ (hsame row h ∨ hsame row p ∨ hsame row n))
            (fun _row : BHist =>
              hsame p n ∧ PkgSig bundle p pkg ∧ PkgSig bundle bridge pkg)
            hsame := by
  -- BEDC touchpoint anchor: BHist UnaryHistory Cont ProbeBundle Pkg PkgSig hsame SemanticNameCert
  intro packet bridgeRoute bridgePkg
  obtain
    ⟨aUnary, bUnary, _cUnary, _dUnary, _eUnary, _fUnary, _gUnary, routeAB, _routeCD,
      _routeEF, pUnary, sameProvenanceName, provenancePkg⟩ := packet
  have hUnary : UnaryHistory h :=
    unary_cont_closed aUnary bUnary routeAB
  have nUnary : UnaryHistory n :=
    unary_transport pUnary sameProvenanceName
  exact {
    core := {
      carrier_inhabited :=
        Exists.intro h
          ⟨Or.inl (hsame_refl h), hUnary, provenancePkg⟩
      equiv_refl := by
        intro row _source
        exact hsame_refl row
      equiv_symm := by
        intro _row _row' sameRows
        exact hsame_symm sameRows
      equiv_trans := by
        intro _row _row' _row'' sameLeft sameRight
        exact hsame_trans sameLeft sameRight
      carrier_respects_equiv := by
        intro row row' sameRows source
        obtain ⟨sourceRow, sourceHUnary, sourcePkg⟩ := source
        have sameRow'Row : hsame row' row :=
          hsame_symm sameRows
        have sourceRow' : hsame row' h ∨ hsame row' p ∨ hsame row' n := by
          cases sourceRow with
          | inl sameRowH =>
              exact Or.inl (hsame_trans sameRow'Row sameRowH)
          | inr rest =>
              cases rest with
              | inl sameRowP =>
                  exact Or.inr (Or.inl (hsame_trans sameRow'Row sameRowP))
              | inr sameRowN =>
                  exact Or.inr (Or.inr (hsame_trans sameRow'Row sameRowN))
        exact ⟨sourceRow', sourceHUnary, sourcePkg⟩
    }
    pattern_sound := by
      intro row source
      obtain ⟨sourceRow, _sourceHUnary, _sourcePkg⟩ := source
      have rowUnary : UnaryHistory row := by
        cases sourceRow with
        | inl sameRowH =>
            exact unary_transport_symm hUnary sameRowH
        | inr rest =>
            cases rest with
            | inl sameRowP =>
                exact unary_transport_symm pUnary sameRowP
            | inr sameRowN =>
                exact unary_transport_symm nUnary sameRowN
      exact ⟨rowUnary, sourceRow⟩
    ledger_sound := by
      intro _row _source
      exact ⟨sameProvenanceName, provenancePkg, bridgePkg⟩
  }

theorem AxisZeckendorfCannotClaimRegistryPacket_negative_refusal_coverage [AskSetup]
    [PackageSetup] {a b c d e f g h p n negative audit : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    AxisZeckendorfCannotClaimRegistryPacket a b c d e f g h p n bundle pkg →
      (hsame negative a ∨ hsame negative b ∨ hsame negative c ∨ hsame negative d) →
        Cont h p audit →
          PkgSig bundle audit pkg →
            UnaryHistory negative ∧ Cont a b h ∧ Cont c d h ∧ hsame p n ∧
              PkgSig bundle p pkg ∧ PkgSig bundle audit pkg := by
  -- BEDC touchpoint anchor: BHist UnaryHistory Cont ProbeBundle Pkg PkgSig hsame
  intro packet negativeRow auditRoute auditPkg
  obtain
    ⟨aUnary, bUnary, cUnary, dUnary, _eUnary, _fUnary, _gUnary, routeAB, routeCD,
      _routeEF, _pUnary, sameProvenanceName, provenancePkg⟩ := packet
  have negativeUnary : UnaryHistory negative := by
    cases negativeRow with
    | inl sameA =>
        exact unary_transport_symm aUnary sameA
    | inr rest =>
        cases rest with
        | inl sameB =>
            exact unary_transport_symm bUnary sameB
        | inr rest =>
            cases rest with
            | inl sameC =>
                exact unary_transport_symm cUnary sameC
            | inr sameD =>
                exact unary_transport_symm dUnary sameD
  exact
    ⟨negativeUnary, routeAB, routeCD, sameProvenanceName, provenancePkg, auditPkg⟩

end BEDC.Derived.AxisZeckendorfCannotClaimUp
