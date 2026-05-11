import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.SpectralMeasureUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def SpectralMeasureFiniteAdditivityLedger [AskSetup] [PackageSetup]
    (event projection other union orthogonality additivity : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  UnaryHistory event ∧ UnaryHistory projection ∧ UnaryHistory other ∧
    UnaryHistory orthogonality ∧ Cont projection other union ∧
      Cont union orthogonality additivity ∧ PkgSig bundle additivity pkg

theorem SpectralMeasureOrthogonalFiniteAdditivity_row [AskSetup] [PackageSetup]
    {event projection other union orthogonality additivity event' projection' other' union'
      orthogonality' additivity' : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    SpectralMeasureFiniteAdditivityLedger event projection other union orthogonality additivity
        bundle pkg ->
      hsame event event' -> hsame projection projection' -> hsame other other' ->
        hsame orthogonality orthogonality' -> Cont projection' other' union' ->
          Cont union' orthogonality' additivity' -> PkgSig bundle additivity' pkg ->
            SpectralMeasureFiniteAdditivityLedger event' projection' other' union'
                orthogonality' additivity' bundle pkg ∧
              hsame union union' ∧ hsame additivity additivity' := by
  intro ledger sameEvent sameProjection sameOther sameOrthogonality unionRow' additivityRow'
    pkgSig'
  have eventUnary' : UnaryHistory event' :=
    unary_transport ledger.left sameEvent
  have projectionUnary' : UnaryHistory projection' :=
    unary_transport ledger.right.left sameProjection
  have otherUnary' : UnaryHistory other' :=
    unary_transport ledger.right.right.left sameOther
  have orthogonalityUnary' : UnaryHistory orthogonality' :=
    unary_transport ledger.right.right.right.left sameOrthogonality
  have sameUnion : hsame union union' :=
    cont_respects_hsame sameProjection sameOther ledger.right.right.right.right.left unionRow'
  have unionUnary' : UnaryHistory union' :=
    unary_cont_closed projectionUnary' otherUnary' unionRow'
  have sameAdditivity : hsame additivity additivity' :=
    cont_respects_hsame sameUnion sameOrthogonality ledger.right.right.right.right.right.left
      additivityRow'
  exact
    And.intro
      (And.intro eventUnary'
        (And.intro projectionUnary'
          (And.intro otherUnary'
            (And.intro orthogonalityUnary'
              (And.intro unionRow'
                (And.intro additivityRow' pkgSig'))))))
      (And.intro sameUnion sameAdditivity)

def SpectralMeasureFinitePacket [AskSetup] [PackageSetup]
    (hilbert observable event projection orthogonality additivity transport provenance
      endpoint : BHist)
    (probe : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  UnaryHistory hilbert ∧ UnaryHistory observable ∧ UnaryHistory event ∧
    UnaryHistory projection ∧ UnaryHistory orthogonality ∧ UnaryHistory additivity ∧
      UnaryHistory transport ∧ UnaryHistory provenance ∧ UnaryHistory endpoint ∧
        Cont observable event projection ∧ Cont projection orthogonality additivity ∧
          Cont additivity transport endpoint ∧ PkgSig probe provenance pkg

theorem SpectralMeasureFinitePacket_namecert_obligation_surface [AskSetup] [PackageSetup]
    {hilbert observable event projection orthogonality additivity transport provenance
      endpoint : BHist}
    {probe : ProbeBundle ProbeName} {pkg : Pkg} :
    SpectralMeasureFinitePacket hilbert observable event projection orthogonality additivity
        transport provenance endpoint probe pkg ->
      SemanticNameCert
          (fun row : BHist =>
            exists e : BHist,
              SpectralMeasureFinitePacket hilbert observable event projection orthogonality
                additivity transport provenance e probe pkg ∧ hsame row e)
          (fun row : BHist =>
            exists e : BHist,
              SpectralMeasureFinitePacket hilbert observable event projection orthogonality
                additivity transport provenance e probe pkg ∧ hsame row e)
          (fun row : BHist =>
            exists e : BHist,
              SpectralMeasureFinitePacket hilbert observable event projection orthogonality
                additivity transport provenance e probe pkg ∧ hsame row e)
          hsame ∧
        Cont observable event projection ∧ Cont projection orthogonality additivity ∧
          Cont additivity transport endpoint ∧ PkgSig probe provenance pkg := by
  intro packet
  have endpointSource :
      (fun row : BHist =>
        exists e : BHist,
          SpectralMeasureFinitePacket hilbert observable event projection orthogonality
            additivity transport provenance e probe pkg ∧ hsame row e) endpoint :=
    Exists.intro endpoint (And.intro packet (hsame_refl endpoint))
  have cert :
      SemanticNameCert
          (fun row : BHist =>
            exists e : BHist,
              SpectralMeasureFinitePacket hilbert observable event projection orthogonality
                additivity transport provenance e probe pkg ∧ hsame row e)
          (fun row : BHist =>
            exists e : BHist,
              SpectralMeasureFinitePacket hilbert observable event projection orthogonality
                additivity transport provenance e probe pkg ∧ hsame row e)
          (fun row : BHist =>
            exists e : BHist,
              SpectralMeasureFinitePacket hilbert observable event projection orthogonality
                additivity transport provenance e probe pkg ∧ hsame row e)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro endpoint endpointSource
      equiv_refl := by
        intro row _carrier
        exact hsame_refl row
      equiv_symm := by
        intro row row' sameRows
        exact hsame_symm sameRows
      equiv_trans := by
        intro row row' row'' sameRow sameRow'
        exact hsame_trans sameRow sameRow'
      carrier_respects_equiv := by
        intro row row' sameRows carrierRow
        cases carrierRow with
        | intro e endpointWitness =>
            exact Exists.intro e
              (And.intro endpointWitness.left
                (hsame_trans (hsame_symm sameRows) endpointWitness.right))
    }
    pattern_sound := by
      intro _row source
      exact source
    ledger_sound := by
      intro _row source
      exact source
  }
  exact And.intro cert
    (And.intro packet.right.right.right.right.right.right.right.right.right.left
      (And.intro packet.right.right.right.right.right.right.right.right.right.right.left
        (And.intro packet.right.right.right.right.right.right.right.right.right.right.right.left
          packet.right.right.right.right.right.right.right.right.right.right.right.right)))

end BEDC.Derived.SpectralMeasureUp
