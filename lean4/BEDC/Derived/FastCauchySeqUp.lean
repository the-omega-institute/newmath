import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.FastCauchySeqUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def FastCauchySeqPacket [AskSetup] [PackageSetup]
    (stream modulus endpoint radius comparison transportWindow regWindow sealBoundary certRow : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  UnaryHistory stream ∧ UnaryHistory modulus ∧ UnaryHistory endpoint ∧ UnaryHistory radius ∧
    UnaryHistory comparison ∧ UnaryHistory transportWindow ∧ UnaryHistory regWindow ∧
      UnaryHistory sealBoundary ∧ UnaryHistory certRow ∧ Cont stream modulus transportWindow ∧
        Cont endpoint radius comparison ∧ Cont comparison transportWindow regWindow ∧
          Cont regWindow sealBoundary certRow ∧ PkgSig bundle regWindow pkg

def FastCauchySeqRegSeqRatWindow [AskSetup] [PackageSetup]
    (stream modulus endpoint radius comparison transportWindow regWindow : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  UnaryHistory stream ∧ UnaryHistory modulus ∧ UnaryHistory endpoint ∧ UnaryHistory radius ∧
    UnaryHistory comparison ∧ UnaryHistory transportWindow ∧ UnaryHistory regWindow ∧
      Cont stream modulus transportWindow ∧ Cont endpoint radius comparison ∧
        Cont comparison transportWindow regWindow ∧ PkgSig bundle regWindow pkg

theorem FastCauchySeqPacket_regseqrat_forgetful_handoff [AskSetup] [PackageSetup]
    {stream modulus endpoint radius comparison transportWindow regWindow sealBoundary certRow : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    FastCauchySeqPacket stream modulus endpoint radius comparison transportWindow regWindow
        sealBoundary certRow bundle pkg ->
      FastCauchySeqRegSeqRatWindow stream modulus endpoint radius comparison transportWindow
          regWindow bundle pkg ∧
        Cont stream modulus transportWindow ∧ Cont endpoint radius comparison ∧
          Cont comparison transportWindow regWindow ∧ PkgSig bundle regWindow pkg := by
  intro packet
  cases packet with
  | intro streamUnary rest =>
      cases rest with
      | intro modulusUnary rest =>
          cases rest with
          | intro endpointUnary rest =>
              cases rest with
              | intro radiusUnary rest =>
                  cases rest with
                  | intro comparisonUnary rest =>
                      cases rest with
                      | intro transportUnary rest =>
                          cases rest with
                          | intro regUnary rest =>
                              cases rest with
                              | intro _sealUnary rest =>
                                  cases rest with
                                  | intro _certUnary rest =>
                                      cases rest with
                                      | intro streamModulusRow rest =>
                                          cases rest with
                                          | intro endpointRadiusRow rest =>
                                              cases rest with
                                              | intro comparisonTransportRow rest =>
                                                  cases rest with
                                                  | intro _certRow pkgRow =>
                                                      constructor
                                                      · exact
                                                          ⟨streamUnary, modulusUnary,
                                                            endpointUnary, radiusUnary,
                                                            comparisonUnary, transportUnary,
                                                            regUnary, streamModulusRow,
                                                            endpointRadiusRow,
                                                            comparisonTransportRow, pkgRow⟩
                                                      · exact
                                                          ⟨streamModulusRow, endpointRadiusRow,
                                                            comparisonTransportRow, pkgRow⟩

theorem FastCauchySeqPacket_real_seal_consumer_boundary [AskSetup] [PackageSetup]
    {stream modulus endpoint radius comparison transportWindow regWindow sealBoundary certRow
      : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    FastCauchySeqPacket stream modulus endpoint radius comparison transportWindow regWindow
        sealBoundary certRow bundle pkg ->
      UnaryHistory stream ∧ UnaryHistory modulus ∧ UnaryHistory endpoint ∧
        UnaryHistory radius ∧ UnaryHistory comparison ∧ UnaryHistory transportWindow ∧
          UnaryHistory regWindow ∧ UnaryHistory sealBoundary ∧ UnaryHistory certRow ∧
            Cont regWindow sealBoundary certRow ∧ PkgSig bundle regWindow pkg := by
  intro packet
  obtain ⟨streamUnary, modulusUnary, endpointUnary, radiusUnary, comparisonUnary,
    transportUnary, regUnary, sealUnary, certUnary, _streamModulusRow, _endpointRadiusRow,
    _comparisonTransportRow, certRowRoute, pkgRow⟩ := packet
  exact
    ⟨streamUnary, modulusUnary, endpointUnary, radiusUnary, comparisonUnary, transportUnary,
      regUnary, sealUnary, certUnary, certRowRoute, pkgRow⟩

theorem FastCauchySeqPacket_public_explicit_rate_export [AskSetup] [PackageSetup]
    {stream modulus endpoint radius comparison transportWindow regWindow sealBoundary certRow
      publicRow : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    FastCauchySeqPacket stream modulus endpoint radius comparison transportWindow regWindow
        sealBoundary certRow bundle pkg ->
      Cont regWindow certRow publicRow ->
        PkgSig bundle publicRow pkg ->
          FastCauchySeqRegSeqRatWindow stream modulus endpoint radius comparison
              transportWindow regWindow bundle pkg ∧
            UnaryHistory publicRow ∧ Cont stream modulus transportWindow ∧
              Cont endpoint radius comparison ∧ Cont comparison transportWindow regWindow ∧
                Cont regWindow certRow publicRow ∧ PkgSig bundle publicRow pkg := by
  intro packet publicRoute publicPkg
  obtain ⟨streamUnary, modulusUnary, endpointUnary, radiusUnary, comparisonUnary,
    transportUnary, regUnary, _sealUnary, certUnary, streamModulusRow, endpointRadiusRow,
    comparisonTransportRow, _certRowRoute, regPkg⟩ := packet
  have publicUnary : UnaryHistory publicRow :=
    unary_cont_closed regUnary certUnary publicRoute
  exact
    ⟨⟨streamUnary, modulusUnary, endpointUnary, radiusUnary, comparisonUnary, transportUnary,
        regUnary, streamModulusRow, endpointRadiusRow, comparisonTransportRow, regPkg⟩,
      publicUnary, streamModulusRow, endpointRadiusRow, comparisonTransportRow, publicRoute,
      publicPkg⟩

theorem FastCauchySeqPacket_semantic_name_certificate [AskSetup] [PackageSetup]
    {stream modulus endpoint radius comparison transportWindow regWindow sealBoundary certRow
      : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    FastCauchySeqPacket stream modulus endpoint radius comparison transportWindow regWindow
        sealBoundary certRow bundle pkg ->
      SemanticNameCert
        (fun row : BHist =>
          FastCauchySeqPacket stream modulus endpoint radius comparison transportWindow regWindow
            sealBoundary certRow bundle pkg ∧ hsame row certRow)
        (fun row : BHist =>
          FastCauchySeqPacket stream modulus endpoint radius comparison transportWindow regWindow
            sealBoundary certRow bundle pkg ∧ hsame row certRow)
        (fun row : BHist =>
          FastCauchySeqPacket stream modulus endpoint radius comparison transportWindow regWindow
            sealBoundary certRow bundle pkg ∧ hsame row certRow)
        hsame := by
  intro packet
  exact {
    core := {
      carrier_inhabited :=
        Exists.intro certRow (And.intro packet (hsame_refl certRow))
      equiv_refl := by
        intro row _source
        exact hsame_refl row
      equiv_symm := by
        intro row row' sameRows
        exact hsame_symm sameRows
      equiv_trans := by
        intro row row' row'' sameLeft sameRight
        exact hsame_trans sameLeft sameRight
      carrier_respects_equiv := by
        intro row row' sameRows source
        exact And.intro source.left (hsame_trans (hsame_symm sameRows) source.right)
    }
    pattern_sound := by
      intro _row source
      exact source
    ledger_sound := by
      intro _row source
      exact source
  }

end BEDC.Derived.FastCauchySeqUp
