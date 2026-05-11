import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.FastCauchySeqUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
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

end BEDC.Derived.FastCauchySeqUp
