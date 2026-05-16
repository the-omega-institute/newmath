import BEDC.Derived.UniformCauchyCriterionUp

namespace BEDC.Derived.UniformCauchyCriterionUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem UniformCauchyCriterionPacket_diagonal_uniqueness_exit [AskSetup] [PackageSetup]
    {index windows modulus tolerance tail sealRow transports routes provenance name diagonalRead
      tailRead realRead classifierRead completionRead phaseRead hostTail : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    UniformCauchyCriterionPacket index windows modulus tolerance tail sealRow transports routes
        provenance name bundle pkg ->
      Cont index windows diagonalRead ->
        Cont diagonalRead tail tailRead ->
          Cont tail sealRow realRead ->
            Cont tailRead realRead classifierRead ->
              Cont classifierRead provenance completionRead ->
                Cont completionRead name phaseRead ->
                  PkgSig bundle phaseRead pkg ->
                    UnaryHistory diagonalRead ∧ UnaryHistory tailRead ∧
                      UnaryHistory realRead ∧ UnaryHistory classifierRead ∧
                        UnaryHistory completionRead ∧ UnaryHistory phaseRead ∧
                          hsame modulus diagonalRead ∧ Cont diagonalRead tail tailRead ∧
                            Cont tailRead realRead classifierRead ∧
                              Cont classifierRead provenance completionRead ∧
                                PkgSig bundle name pkg ∧ PkgSig bundle phaseRead pkg ∧
                                  (Cont classifierRead (BHist.e0 hostTail) tailRead ->
                                    False) ∧
                                    (Cont classifierRead (BHist.e1 hostTail) tailRead ->
                                      False) := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame UnaryHistory
  intro packet indexWindowsDiagonal diagonalTailRead tailSealReal tailReadRealClassifier
    classifierProvenanceCompletion completionNamePhase phasePkg
  obtain ⟨indexUnary, windowsUnary, modulusUnary, _toleranceUnary, tailUnary, sealRowUnary,
    _transportsUnary, _routesUnary, provenanceUnary, nameUnary, indexWindowsModulus,
    _modulusToleranceTail, _tailSealRowTransports, _transportsRoutesProvenance, namePkg⟩ :=
    packet
  have diagonalUnary : UnaryHistory diagonalRead :=
    unary_cont_closed indexUnary windowsUnary indexWindowsDiagonal
  have tailReadUnary : UnaryHistory tailRead :=
    unary_cont_closed diagonalUnary tailUnary diagonalTailRead
  have realReadUnary : UnaryHistory realRead :=
    unary_cont_closed tailUnary sealRowUnary tailSealReal
  have classifierUnary : UnaryHistory classifierRead :=
    unary_cont_closed tailReadUnary realReadUnary tailReadRealClassifier
  have completionUnary : UnaryHistory completionRead :=
    unary_cont_closed classifierUnary provenanceUnary classifierProvenanceCompletion
  have phaseUnary : UnaryHistory phaseRead :=
    unary_cont_closed completionUnary nameUnary completionNamePhase
  have sameModulus : hsame modulus diagonalRead :=
    cont_respects_hsame (hsame_refl index) (hsame_refl windows) indexWindowsModulus
      indexWindowsDiagonal
  exact
    ⟨diagonalUnary, tailReadUnary, realReadUnary, classifierUnary, completionUnary, phaseUnary,
      sameModulus, diagonalTailRead, tailReadRealClassifier, classifierProvenanceCompletion,
      namePkg, phasePkg,
      (fun hostReturn =>
        cont_mutual_extension_right_tail_absurd.left tailReadRealClassifier hostReturn),
      (fun hostReturn =>
        cont_mutual_extension_right_tail_absurd.right tailReadRealClassifier hostReturn)⟩

end BEDC.Derived.UniformCauchyCriterionUp
