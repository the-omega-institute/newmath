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

theorem RegularCauchyNegationCarrier_diagonal_limit_readout [AskSetup] [PackageSetup]
    {source window dyadic classifier flipped sealRow transportRow route provenance name
      diagonalRead limitRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    RegularCauchyNegationCarrier source window dyadic classifier flipped sealRow transportRow
        route provenance name bundle pkg ->
      Cont window dyadic diagonalRead ->
        Cont classifier flipped limitRead ->
          PkgSig bundle diagonalRead pkg ->
            PkgSig bundle limitRead pkg ->
              UnaryHistory diagonalRead ∧ UnaryHistory limitRead ∧
                Cont source window dyadic ∧ Cont dyadic classifier flipped ∧
                  Cont window dyadic diagonalRead ∧ Cont classifier flipped limitRead ∧
                    PkgSig bundle provenance pkg ∧ PkgSig bundle diagonalRead pkg ∧
                      PkgSig bundle limitRead pkg := by
  intro carrier windowDyadicRead classifierFlippedRead diagonalReadPkg limitReadPkg
  obtain ⟨sourceUnary, windowUnary, dyadicUnary, classifierUnary, flippedUnary,
    _sealUnary, _transportUnary, _routeUnary, _provenanceUnary, _nameUnary,
    sourceWindowDyadic, dyadicClassifierFlipped, _flippedSealTransport,
    _transportRouteProvenance, _sealProvenanceName, provenancePkg, _namePkg⟩ := carrier
  have diagonalReadUnary : UnaryHistory diagonalRead :=
    unary_cont_closed windowUnary dyadicUnary windowDyadicRead
  have limitReadUnary : UnaryHistory limitRead :=
    unary_cont_closed classifierUnary flippedUnary classifierFlippedRead
  exact
    ⟨diagonalReadUnary, limitReadUnary, sourceWindowDyadic, dyadicClassifierFlipped,
      windowDyadicRead, classifierFlippedRead, provenancePkg, diagonalReadPkg, limitReadPkg⟩

end BEDC.Derived.RegularCauchyNegationUp
