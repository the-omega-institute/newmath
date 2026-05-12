import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

/-!
# CauchyRegularizationUp finite carrier and semantic NameCert surface.
-/

namespace BEDC.Derived.CauchyRegularizationUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

/-- Finite carrier surface for Cauchy regularization readback. -/
def CauchyRegularizationCarrier [AskSetup] [PackageSetup]
    (streamRow modulusRow dyadicRow windowRow regseqRow sealRow transportRow routeRow
      nameRow : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  UnaryHistory streamRow ∧ UnaryHistory modulusRow ∧ UnaryHistory dyadicRow ∧
    UnaryHistory windowRow ∧ UnaryHistory regseqRow ∧ UnaryHistory sealRow ∧
      UnaryHistory transportRow ∧ UnaryHistory routeRow ∧ UnaryHistory nameRow ∧
        Cont streamRow modulusRow transportRow ∧ Cont dyadicRow windowRow routeRow ∧
          hsame sealRow (append regseqRow routeRow) ∧ PkgSig bundle sealRow pkg

theorem CauchyRegularizationCarrier_namecert_obligation_surface [AskSetup] [PackageSetup]
    {streamRow modulusRow dyadicRow windowRow regseqRow sealRow transportRow routeRow
      nameRow : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CauchyRegularizationCarrier streamRow modulusRow dyadicRow windowRow regseqRow
        sealRow transportRow routeRow nameRow bundle pkg →
      SemanticNameCert
        (fun row : BHist =>
          CauchyRegularizationCarrier streamRow modulusRow dyadicRow windowRow
            regseqRow sealRow transportRow routeRow nameRow bundle pkg ∧ hsame row sealRow)
        (fun row : BHist =>
          CauchyRegularizationCarrier streamRow modulusRow dyadicRow windowRow
            regseqRow sealRow transportRow routeRow nameRow bundle pkg ∧ hsame row sealRow)
        (fun row : BHist =>
          CauchyRegularizationCarrier streamRow modulusRow dyadicRow windowRow
            regseqRow sealRow transportRow routeRow nameRow bundle pkg ∧ hsame row sealRow)
        hsame := by
  intro carrier
  exact {
    core := {
      carrier_inhabited := Exists.intro sealRow (And.intro carrier rfl)
      equiv_refl := by
        intro row _source
        exact hsame_refl row
      equiv_symm := by
        intro row row' same
        exact hsame_symm same
      equiv_trans := by
        intro row row' row'' same same'
        exact hsame_trans same same'
      carrier_respects_equiv := by
        intro row row' same source
        cases source with
        | intro carrierData sourceSame =>
            cases same
            exact And.intro carrierData sourceSame
    }
    pattern_sound := by
      intro row source
      exact source
    ledger_sound := by
      intro row source
      exact source
  }

def CauchyRegularizationSealRoute [AskSetup] [PackageSetup]
    (streamRow modulusRow dyadicRow windowRow regseqRow sealRow transportRow routeRow nameRow
      sealRead : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  CauchyRegularizationCarrier streamRow modulusRow dyadicRow windowRow regseqRow sealRow
      transportRow routeRow nameRow bundle pkg ∧
    Cont regseqRow routeRow sealRead ∧ PkgSig bundle sealRead pkg

theorem CauchyRegularizationSealRoute_semantic_name_certificate [AskSetup] [PackageSetup]
    {streamRow modulusRow dyadicRow windowRow regseqRow sealRow transportRow routeRow nameRow
      sealRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CauchyRegularizationSealRoute streamRow modulusRow dyadicRow windowRow regseqRow sealRow
        transportRow routeRow nameRow sealRead bundle pkg ->
      SemanticNameCert
        (fun row : BHist =>
          CauchyRegularizationSealRoute streamRow modulusRow dyadicRow windowRow regseqRow
            sealRow transportRow routeRow nameRow sealRead bundle pkg ∧ hsame row sealRead)
        (fun row : BHist =>
          CauchyRegularizationSealRoute streamRow modulusRow dyadicRow windowRow regseqRow
            sealRow transportRow routeRow nameRow sealRead bundle pkg ∧ hsame row sealRead)
        (fun row : BHist =>
          CauchyRegularizationSealRoute streamRow modulusRow dyadicRow windowRow regseqRow
            sealRow transportRow routeRow nameRow sealRead bundle pkg ∧ hsame row sealRead)
        hsame := by
  intro route
  have routeSource := route
  obtain ⟨carrier, regseqRouteRead, _sealReadPkg⟩ := route
  obtain ⟨_streamUnary, _modulusUnary, _dyadicUnary, _windowUnary, regseqUnary,
    _sealUnary, _transportUnary, routeUnary, _nameUnary, _streamModulusTransport,
    _dyadicWindowRoute, _sealAppend, _sealPkg⟩ := carrier
  have _sealReadUnary : UnaryHistory sealRead :=
    unary_cont_closed regseqUnary routeUnary regseqRouteRead
  exact {
    core := {
      carrier_inhabited := Exists.intro sealRead (And.intro routeSource (hsame_refl sealRead))
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
      intro _row source
      exact source
    ledger_sound := by
      intro _row source
      exact source
  }

def CauchyRegularizationFiniteCarrier [AskSetup] [PackageSetup]
    (stream modulus dyadic window regseq realSeal sameRows route provenance namecert endpoint :
      BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  UnaryHistory stream ∧
    UnaryHistory modulus ∧
    UnaryHistory dyadic ∧
    UnaryHistory window ∧
    UnaryHistory regseq ∧
    UnaryHistory realSeal ∧
    UnaryHistory sameRows ∧
    UnaryHistory route ∧
    UnaryHistory provenance ∧
    UnaryHistory namecert ∧
    UnaryHistory endpoint ∧
    Cont stream modulus dyadic ∧
    Cont dyadic window regseq ∧
    Cont regseq realSeal endpoint ∧
    hsame sameRows (append stream modulus) ∧
    hsame route (append dyadic window) ∧
    hsame provenance (append regseq realSeal) ∧
    hsame namecert endpoint ∧
    PkgSig bundle endpoint pkg

theorem CauchyRegularizationFiniteCarrier_namecert_obligation_surface [AskSetup]
    [PackageSetup]
    {stream modulus dyadic window regseq realSeal sameRows route provenance namecert endpoint :
      BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CauchyRegularizationFiniteCarrier stream modulus dyadic window regseq realSeal sameRows route
      provenance namecert endpoint bundle pkg →
      SemanticNameCert
        (fun row : BHist =>
          CauchyRegularizationFiniteCarrier stream modulus dyadic window regseq realSeal sameRows
            route provenance namecert endpoint bundle pkg ∧ hsame row endpoint)
        (fun row : BHist =>
          CauchyRegularizationFiniteCarrier stream modulus dyadic window regseq realSeal sameRows
            route provenance namecert endpoint bundle pkg ∧ hsame row endpoint)
        (fun row : BHist =>
          CauchyRegularizationFiniteCarrier stream modulus dyadic window regseq realSeal sameRows
            route provenance namecert endpoint bundle pkg ∧ hsame row endpoint)
        hsame := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg hsame Cont
  intro carrier
  exact {
    core := {
      carrier_inhabited := Exists.intro endpoint (And.intro carrier rfl)
      equiv_refl := by
        intro h _source
        rfl
      equiv_symm := by
        intro h k same
        exact same.symm
      equiv_trans := by
        intro h k r left right
        exact left.trans right
      carrier_respects_equiv := by
        intro h k same source
        exact And.intro source.left (same.symm.trans source.right)
    }
    pattern_sound := by
      intro h source
      exact source
    ledger_sound := by
      intro h source
      exact source
  }

theorem CauchyRegularizationFiniteCarrier_regular_sequence_handoff [AskSetup]
    [PackageSetup]
    {stream modulus dyadic window regseq realSeal sameRows route provenance namecert endpoint :
      BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CauchyRegularizationFiniteCarrier stream modulus dyadic window regseq realSeal sameRows route
      provenance namecert endpoint bundle pkg →
      Cont (append (append stream modulus) window) realSeal endpoint ∧
        hsame endpoint (append (append (append stream modulus) window) realSeal) ∧
          PkgSig bundle endpoint pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg hsame Cont
  intro carrier
  cases carrier with
  | intro _streamUnary rest =>
      cases rest with
      | intro _modulusUnary rest =>
          cases rest with
          | intro _dyadicUnary rest =>
              cases rest with
              | intro _windowUnary rest =>
                  cases rest with
                  | intro _regseqUnary rest =>
                      cases rest with
                      | intro _realSealUnary rest =>
                          cases rest with
                          | intro _sameRowsUnary rest =>
                              cases rest with
                              | intro _routeUnary rest =>
                                  cases rest with
                                  | intro _provenanceUnary rest =>
                                      cases rest with
                                      | intro _namecertUnary rest =>
                                          cases rest with
                                          | intro _endpointUnary rest =>
                                              cases rest with
                                              | intro streamToDyadic rest =>
                                                  cases rest with
                                                  | intro dyadicToRegseq rest =>
                                                      cases rest with
                                                      | intro regseqToEndpoint rest =>
                                                          cases rest with
                                                          | intro _sameRows rest =>
                                                              cases rest with
                                                              | intro _route rest =>
                                                                  cases rest with
                                                                  | intro _provenance rest =>
                                                                      cases rest with
                                                                      | intro _namecert pkgSig =>
                                                                          cases streamToDyadic
                                                                          cases dyadicToRegseq
                                                                          cases regseqToEndpoint
                                                                          exact And.intro rfl
                                                                            (And.intro rfl pkgSig)

end BEDC.Derived.CauchyRegularizationUp
