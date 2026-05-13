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
                  Cont c d h ∧ Cont e f h ∧ hsame p n ∧ PkgSig bundle p pkg

theorem AxisZeckendorfCannotClaimRegistryPacket_source_row_coverage [AskSetup] [PackageSetup]
    {a b c d e f g h p n : BHist} {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    AxisZeckendorfCannotClaimRegistryPacket a b c d e f g h p n bundle pkg ->
      UnaryHistory a ∧ UnaryHistory b ∧ UnaryHistory c ∧ UnaryHistory d ∧
        UnaryHistory e ∧ UnaryHistory f ∧ UnaryHistory g ∧ Cont a b h ∧ Cont c d h ∧
          Cont e f h ∧ hsame p n ∧ PkgSig bundle p pkg := by
  intro packet
  obtain
    ⟨aUnary, bUnary, cUnary, dUnary, eUnary, fUnary, gUnary, routeAB, routeCD, routeEF,
      sameProvenanceName, pkgSig⟩ := packet
  exact
    ⟨aUnary, bUnary, cUnary, dUnary, eUnary, fUnary, gUnary, routeAB, routeCD, routeEF,
      sameProvenanceName, pkgSig⟩

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
      sameProvenanceName, _pkgSig⟩ := packet
  have routeSame : hsame h h' := cont_respects_hsame sameA sameB routeAB routeAB'
  have transportedProvenanceName : hsame p' n' :=
    hsame_trans (hsame_symm sameP) (hsame_trans sameProvenanceName sameN)
  constructor
  · exact
      ⟨unary_transport aUnary sameA, unary_transport bUnary sameB,
        unary_transport cUnary sameC, unary_transport dUnary sameD,
        unary_transport eUnary sameE, unary_transport fUnary sameF,
        unary_transport gUnary sameG, routeAB', routeCD', routeEF', transportedProvenanceName,
        pkgSig'⟩
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
      _routeEF, sameProvenanceName, pkgSig⟩ := packet
  have sameRootDownstream : hsame h downstream :=
    cont_deterministic rootRoute downstreamRoute
  exact ⟨sameRootDownstream, sameProvenanceName, pkgSig⟩

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
      _sameProvenanceName, _pkgSig⟩ := packet
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

end BEDC.Derived.AxisZeckendorfCannotClaimUp
