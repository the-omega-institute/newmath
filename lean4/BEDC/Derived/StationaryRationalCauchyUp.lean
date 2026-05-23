import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Cont.Cancellation
import BEDC.FKernel.Hist
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.StationaryRationalCauchyUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def StationaryRationalCauchyCarrier [AskSetup] [PackageSetup]
    (q schedule regseq dyadic «seal» provenance cert endpoint : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  UnaryHistory q ∧ UnaryHistory schedule ∧ UnaryHistory regseq ∧ UnaryHistory dyadic ∧
    UnaryHistory «seal» ∧ UnaryHistory provenance ∧ UnaryHistory cert ∧
      Cont q schedule regseq ∧ Cont regseq dyadic «seal» ∧ Cont provenance cert endpoint ∧
        PkgSig bundle endpoint pkg

def StationaryRationalCauchyBHistCarrier [AskSetup] [PackageSetup]
    (seed stream regular ledger realSeal provenance nameCert diagonalRoute : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  UnaryHistory seed ∧ UnaryHistory stream ∧ UnaryHistory regular ∧
    UnaryHistory ledger ∧ UnaryHistory realSeal ∧ UnaryHistory provenance ∧
      UnaryHistory nameCert ∧ UnaryHistory diagonalRoute ∧
        hsame diagonalRoute (append regular stream) ∧ PkgSig bundle realSeal pkg

theorem StationaryRationalCauchyCarrier_namecert_obligations [AskSetup] [PackageSetup]
    {q schedule regseq dyadic «seal» provenance cert endpoint : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    StationaryRationalCauchyCarrier q schedule regseq dyadic «seal» provenance cert endpoint
        bundle pkg ->
      UnaryHistory q ∧ Cont q schedule regseq ∧ Cont regseq dyadic «seal» ∧
        PkgSig bundle endpoint pkg ∧
          SemanticNameCert
            (fun row : BHist =>
              StationaryRationalCauchyCarrier q schedule regseq dyadic «seal» provenance cert
                endpoint bundle pkg ∧ hsame row endpoint)
            (fun row : BHist =>
              StationaryRationalCauchyCarrier q schedule regseq dyadic «seal» provenance cert
                endpoint bundle pkg ∧ hsame row endpoint)
            (fun row : BHist =>
              StationaryRationalCauchyCarrier q schedule regseq dyadic «seal» provenance cert
                endpoint bundle pkg ∧ hsame row endpoint)
            hsame := by
  intro carrier
  have carrierCopy :
      StationaryRationalCauchyCarrier q schedule regseq dyadic «seal» provenance cert endpoint
          bundle pkg :=
    carrier
  obtain ⟨qUnary, _scheduleUnary, _regseqUnary, _dyadicUnary, _sealUnary, _provenanceUnary,
    _certUnary, regseqRow, sealRow, _endpointRow, pkgRow⟩ := carrier
  have endpointSource :
      StationaryRationalCauchyCarrier q schedule regseq dyadic «seal» provenance cert endpoint
          bundle pkg ∧ hsame endpoint endpoint :=
    And.intro carrierCopy (hsame_refl endpoint)
  have semantic :
      SemanticNameCert
        (fun row : BHist =>
          StationaryRationalCauchyCarrier q schedule regseq dyadic «seal» provenance cert endpoint
            bundle pkg ∧ hsame row endpoint)
        (fun row : BHist =>
          StationaryRationalCauchyCarrier q schedule regseq dyadic «seal» provenance cert endpoint
            bundle pkg ∧ hsame row endpoint)
        (fun row : BHist =>
          StationaryRationalCauchyCarrier q schedule regseq dyadic «seal» provenance cert endpoint
            bundle pkg ∧ hsame row endpoint)
        hsame := {
    core := {
      carrier_inhabited := Exists.intro endpoint endpointSource
      equiv_refl := by
        intro row _source
        exact hsame_refl row
      equiv_symm := by
        intro _row _row' same
        exact hsame_symm same
      equiv_trans := by
        intro _row _row' _row'' sameLeft sameRight
        exact hsame_trans sameLeft sameRight
      carrier_respects_equiv := by
        intro row row' same sourceRow
        exact And.intro sourceRow.left (hsame_trans (hsame_symm same) sourceRow.right)
    }
    pattern_sound := by
      intro _row sourceRow
      exact sourceRow
    ledger_sound := by
      intro _row sourceRow
      exact sourceRow
  }
  exact And.intro qUnary
    (And.intro regseqRow (And.intro sealRow (And.intro pkgRow semantic)))

theorem StationaryRationalCauchyCarrier_ledger_exactness [AskSetup] [PackageSetup]
    {q schedule regseq dyadic «seal» provenance cert endpoint : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    StationaryRationalCauchyCarrier q schedule regseq dyadic «seal» provenance cert endpoint
        bundle pkg →
      UnaryHistory q ∧ UnaryHistory schedule ∧ UnaryHistory regseq ∧
        UnaryHistory dyadic ∧ UnaryHistory «seal» ∧
          hsame regseq (append q schedule) ∧
            hsame «seal» (append regseq dyadic) ∧
              PkgSig bundle endpoint pkg := by
  intro carrier
  obtain ⟨qUnary, scheduleUnary, regseqUnary, dyadicUnary, sealUnary, _provenanceUnary,
    _certUnary, regseqRow, sealRow, _endpointRow, pkgRow⟩ := carrier
  exact
    And.intro qUnary
      (And.intro scheduleUnary
        (And.intro regseqUnary
          (And.intro dyadicUnary
            (And.intro sealUnary
              (And.intro regseqRow
                (And.intro sealRow pkgRow))))))

theorem StationaryRationalCauchyBHistCarrier_diagonal_handoff [AskSetup] [PackageSetup]
    {seed stream regular ledger realSeal provenance nameCert diagonalRoute readRoute : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    StationaryRationalCauchyBHistCarrier seed stream regular ledger realSeal provenance nameCert
        diagonalRoute bundle pkg ->
      Cont regular stream diagonalRoute ->
        Cont diagonalRoute seed readRoute ->
          UnaryHistory readRoute ∧ hsame diagonalRoute (append regular stream) ∧
            PkgSig bundle realSeal pkg := by
  intro carrier _diagonalRoute routeRead
  obtain ⟨seedUnary, _streamUnary, _regularUnary, _ledgerUnary, _realSealUnary,
    _provenanceUnary, _nameCertUnary, diagonalUnary, diagonalEq, pkgRow⟩ := carrier
  have readUnary : UnaryHistory readRoute :=
    unary_cont_closed diagonalUnary seedUnary routeRead
  exact ⟨readUnary, diagonalEq, pkgRow⟩

theorem StationaryRationalCauchyUp_StdBridge [AskSetup] [PackageSetup]
    {seed stream regular ledger realSeal provenance nameCert diagonalRoute readRoute : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    StationaryRationalCauchyBHistCarrier seed stream regular ledger realSeal provenance nameCert
        diagonalRoute bundle pkg ->
      Cont regular stream diagonalRoute ->
        Cont diagonalRoute seed readRoute ->
          SemanticNameCert
              (fun row : BHist => hsame row diagonalRoute /\ UnaryHistory row /\
                PkgSig bundle realSeal pkg)
              (fun row : BHist => UnaryHistory regular /\ UnaryHistory stream /\
                hsame row (append regular stream))
              (fun row : BHist => PkgSig bundle realSeal pkg /\ Cont regular stream row)
              (fun row row' : BHist => PkgSig bundle realSeal pkg /\ hsame row row') /\
            UnaryHistory readRoute := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg SemanticNameCert hsame Cont
  intro carrier diagonalCont routeRead
  obtain ⟨seedUnary, streamUnary, regularUnary, _ledgerUnary, _realSealUnary,
    _provenanceUnary, _nameCertUnary, diagonalUnary, diagonalEq, pkgRow⟩ := carrier
  have readUnary : UnaryHistory readRoute :=
    unary_cont_closed diagonalUnary seedUnary routeRead
  have diagonalSource :
      hsame diagonalRoute diagonalRoute /\ UnaryHistory diagonalRoute /\
        PkgSig bundle realSeal pkg :=
    ⟨hsame_refl diagonalRoute, diagonalUnary, pkgRow⟩
  have semantic :
      SemanticNameCert
        (fun row : BHist => hsame row diagonalRoute /\ UnaryHistory row /\
          PkgSig bundle realSeal pkg)
        (fun row : BHist => UnaryHistory regular /\ UnaryHistory stream /\
          hsame row (append regular stream))
        (fun row : BHist => PkgSig bundle realSeal pkg /\ Cont regular stream row)
        (fun row row' : BHist => PkgSig bundle realSeal pkg /\ hsame row row') := {
    core := {
      carrier_inhabited := Exists.intro diagonalRoute diagonalSource
      equiv_refl := by
        intro row _source
        exact ⟨pkgRow, hsame_refl row⟩
      equiv_symm := by
        intro _row _row' classified
        exact ⟨classified.left, hsame_symm classified.right⟩
      equiv_trans := by
        intro _row _row' _row'' left right
        exact ⟨left.left, hsame_trans left.right right.right⟩
      carrier_respects_equiv := by
        intro row row' classified source
        exact
          ⟨hsame_trans (hsame_symm classified.right) source.left,
            unary_transport source.right.left classified.right,
            classified.left⟩
    }
    pattern_sound := by
      intro row source
      exact ⟨regularUnary, streamUnary, hsame_trans source.left diagonalEq⟩
    ledger_sound := by
      intro row source
      exact
        ⟨source.right.right,
          cont_result_hsame_transport diagonalCont (hsame_symm source.left)⟩
  }
  exact ⟨semantic, readUnary⟩

theorem StationaryRationalCauchyCarrier_classifier_correspondence [AskSetup] [PackageSetup]
    {q schedule regseq dyadic «seal» provenance cert endpoint q' schedule' regseq' dyadic'
      seal' provenance' cert' endpoint' : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    StationaryRationalCauchyCarrier q schedule regseq dyadic «seal» provenance cert endpoint
        bundle pkg ->
      hsame q q' ->
        hsame schedule schedule' ->
          hsame regseq regseq' ->
            hsame dyadic dyadic' ->
              hsame «seal» seal' ->
                hsame provenance provenance' ->
                  hsame cert cert' ->
                    hsame endpoint endpoint' ->
                      PkgSig bundle endpoint' pkg ->
                        StationaryRationalCauchyCarrier q' schedule' regseq' dyadic' seal'
                          provenance' cert' endpoint' bundle pkg := by
  intro carrier sameQ sameSchedule sameRegseq sameDyadic sameSeal sameProvenance sameCert
    sameEndpoint endpointPkg
  obtain ⟨qUnary, scheduleUnary, regseqUnary, dyadicUnary, sealUnary, provenanceUnary, certUnary,
    qScheduleRegseq, regseqDyadicSeal, provenanceCertEndpoint, _endpointPkg⟩ := carrier
  exact
    ⟨unary_transport qUnary sameQ,
      unary_transport scheduleUnary sameSchedule,
      unary_transport regseqUnary sameRegseq,
      unary_transport dyadicUnary sameDyadic,
      unary_transport sealUnary sameSeal,
      unary_transport provenanceUnary sameProvenance,
      unary_transport certUnary sameCert,
      cont_hsame_transport sameQ sameSchedule sameRegseq qScheduleRegseq,
      cont_hsame_transport sameRegseq sameDyadic sameSeal regseqDyadicSeal,
      cont_hsame_transport sameProvenance sameCert sameEndpoint provenanceCertEndpoint,
      endpointPkg⟩

end BEDC.Derived.StationaryRationalCauchyUp
