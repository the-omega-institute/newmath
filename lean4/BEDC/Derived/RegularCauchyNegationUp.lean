import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.RegularCauchyNegationUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def RegularCauchyNegationCarrier [AskSetup] [PackageSetup]
    (source window dyadic classifier flipped sealRow transportRow route provenance name : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  UnaryHistory source ∧ UnaryHistory window ∧ UnaryHistory dyadic ∧
    UnaryHistory classifier ∧ UnaryHistory flipped ∧ UnaryHistory sealRow ∧
      UnaryHistory transportRow ∧ UnaryHistory route ∧ UnaryHistory provenance ∧
        UnaryHistory name ∧ Cont source window dyadic ∧ Cont dyadic classifier flipped ∧
          Cont flipped sealRow transportRow ∧ Cont transportRow route provenance ∧
            Cont sealRow provenance name ∧ PkgSig bundle provenance pkg ∧
              PkgSig bundle name pkg

theorem RegularCauchyNegationCarrier_namecert_obligations [AskSetup] [PackageSetup]
    {source window dyadic classifier flipped sealRow transportRow route provenance
      name : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    RegularCauchyNegationCarrier source window dyadic classifier flipped sealRow transportRow
        route provenance name bundle pkg ->
      SemanticNameCert
        (fun row : BHist =>
          RegularCauchyNegationCarrier source window dyadic classifier flipped sealRow
            transportRow route provenance name bundle pkg ∧ hsame row sealRow)
        (fun row : BHist =>
          RegularCauchyNegationCarrier source window dyadic classifier flipped sealRow
            transportRow route provenance name bundle pkg ∧ hsame row sealRow)
        (fun row : BHist =>
          RegularCauchyNegationCarrier source window dyadic classifier flipped sealRow
            transportRow route provenance name bundle pkg ∧ hsame row sealRow)
        hsame := by
  -- BEDC touchpoint anchor: BHist Cont PkgSig hsame SemanticNameCert
  intro carrier
  exact {
    core := {
      carrier_inhabited := Exists.intro sealRow (And.intro carrier (hsame_refl sealRow))
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
        intro _row _row' sameRows sourceRow
        exact And.intro sourceRow.left (hsame_trans (hsame_symm sameRows) sourceRow.right)
    }
    pattern_sound := by
      intro _row sourceRow
      exact sourceRow
    ledger_sound := by
      intro _row sourceRow
      exact sourceRow
  }

theorem RegularCauchyNegationCarrier_public_seal_export [AskSetup] [PackageSetup]
    {source window dyadic classifier flipped sealRow transportRow route provenance name
      realBoundary : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    RegularCauchyNegationCarrier source window dyadic classifier flipped sealRow transportRow
        route provenance name bundle pkg →
      Cont name route realBoundary →
        PkgSig bundle realBoundary pkg →
          SemanticNameCert
              (fun row : BHist =>
                RegularCauchyNegationCarrier source window dyadic classifier flipped sealRow
                    transportRow route provenance name bundle pkg ∧ hsame row sealRow)
              (fun row : BHist =>
                RegularCauchyNegationCarrier source window dyadic classifier flipped sealRow
                    transportRow route provenance name bundle pkg ∧ hsame row sealRow)
              (fun row : BHist =>
                RegularCauchyNegationCarrier source window dyadic classifier flipped sealRow
                    transportRow route provenance name bundle pkg ∧ hsame row sealRow)
              hsame ∧
            UnaryHistory sealRow ∧
            UnaryHistory name ∧
            UnaryHistory realBoundary ∧
            Cont sealRow provenance name ∧
            Cont name route realBoundary ∧
            PkgSig bundle name pkg ∧
            PkgSig bundle realBoundary pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont SemanticNameCert hsame
  intro carrier nameRouteBoundary boundaryPkg
  have cert :=
    RegularCauchyNegationCarrier_namecert_obligations carrier
  obtain ⟨_sourceUnary, _windowUnary, _dyadicUnary, _classifierUnary, _flippedUnary,
    sealUnary, _transportUnary, routeUnary, _provenanceUnary, nameUnary,
    _sourceWindowDyadic, _dyadicClassifierFlipped, _flippedSealTransport,
    _transportRouteProvenance, sealProvenanceName, _provenancePkg, namePkg⟩ := carrier
  have boundaryUnary : UnaryHistory realBoundary :=
    unary_cont_closed nameUnary routeUnary nameRouteBoundary
  exact
    ⟨cert, sealUnary, nameUnary, boundaryUnary, sealProvenanceName, nameRouteBoundary, namePkg,
      boundaryPkg⟩

end BEDC.Derived.RegularCauchyNegationUp
