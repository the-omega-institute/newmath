import BEDC.Derived.UniformCauchyCriterionUp

namespace BEDC.Derived.UniformCauchyCriterionUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem UniformCauchyCriterionPacket_diagonal_exit_classifier
    [AskSetup] [PackageSetup]
    {index windows modulus tolerance tail sealRow transports routes provenance name diagonalRead
      tailRead realRead realRead' classifierRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    UniformCauchyCriterionPacket index windows modulus tolerance tail sealRow transports routes
        provenance name bundle pkg ->
      Cont index windows diagonalRead ->
      Cont diagonalRead tail tailRead ->
      Cont tail sealRow realRead ->
      Cont tail sealRow realRead' ->
      Cont tailRead realRead classifierRead ->
      PkgSig bundle classifierRead pkg ->
      UnaryHistory diagonalRead ∧ UnaryHistory tailRead ∧ UnaryHistory realRead ∧
        UnaryHistory classifierRead ∧ hsame realRead realRead' ∧
          Cont diagonalRead tail tailRead ∧ Cont tailRead realRead classifierRead ∧
            PkgSig bundle name pkg ∧ PkgSig bundle classifierRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont UnaryHistory hsame PkgSig
  intro packet indexWindowsDiagonal diagonalTailRead tailSealReal tailSealReal'
    tailReadRealClassifier classifierPkg
  obtain ⟨indexUnary, windowsUnary, _modulusUnary, _toleranceUnary, tailUnary, sealRowUnary,
    _transportsUnary, _routesUnary, _provenanceUnary, _nameUnary, _indexWindowsModulus,
    _modulusToleranceTail, _tailSealTransports, _transportsRoutesProvenance, namePkg⟩ :=
    packet
  have diagonalUnary : UnaryHistory diagonalRead :=
    unary_cont_closed indexUnary windowsUnary indexWindowsDiagonal
  have tailReadUnary : UnaryHistory tailRead :=
    unary_cont_closed diagonalUnary tailUnary diagonalTailRead
  have realReadUnary : UnaryHistory realRead :=
    unary_cont_closed tailUnary sealRowUnary tailSealReal
  have classifierUnary : UnaryHistory classifierRead :=
    unary_cont_closed tailReadUnary realReadUnary tailReadRealClassifier
  have sameRealRead : hsame realRead realRead' :=
    cont_respects_hsame (hsame_refl tail) (hsame_refl sealRow) tailSealReal tailSealReal'
  exact
    ⟨diagonalUnary, tailReadUnary, realReadUnary, classifierUnary, sameRealRead,
      diagonalTailRead, tailReadRealClassifier, namePkg, classifierPkg⟩

end BEDC.Derived.UniformCauchyCriterionUp
