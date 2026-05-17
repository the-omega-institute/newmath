import BEDC.Derived.UniformCauchyCriterionUp

namespace BEDC.Derived.UniformCauchyCriterionUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem UniformCauchyCriterionPacket_diagonal_structural_face_coverage
    [AskSetup] [PackageSetup]
    {index windows modulus tolerance tail sealRow transports routes provenance name diagonalRead
      realRead completionRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    UniformCauchyCriterionPacket index windows modulus tolerance tail sealRow transports routes
        provenance name bundle pkg ->
      Cont windows sealRow diagonalRead ->
        Cont diagonalRead transports realRead ->
          Cont realRead routes completionRead ->
            PkgSig bundle completionRead pkg ->
              UnaryHistory windows ∧ UnaryHistory tolerance ∧ UnaryHistory tail ∧
                UnaryHistory sealRow ∧ UnaryHistory transports ∧ UnaryHistory routes ∧
                  UnaryHistory provenance ∧ UnaryHistory diagonalRead ∧ UnaryHistory realRead ∧
                    UnaryHistory completionRead ∧ Cont index windows modulus ∧
                      Cont modulus tolerance tail ∧ Cont windows sealRow diagonalRead ∧
                        Cont diagonalRead transports realRead ∧
                          Cont realRead routes completionRead ∧ PkgSig bundle name pkg ∧
                            PkgSig bundle completionRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont UnaryHistory
  intro packet windowsSealDiagonal diagonalTransportsReal realRoutesCompletion completionPkg
  obtain ⟨_indexUnary, windowsUnary, _modulusUnary, toleranceUnary, tailUnary, sealRowUnary,
    transportsUnary, routesUnary, provenanceUnary, _nameUnary, indexWindowsModulus,
    modulusToleranceTail, _tailSealRowTransports, _transportsRoutesProvenance, namePkg⟩ :=
    packet
  have diagonalUnary : UnaryHistory diagonalRead :=
    unary_cont_closed windowsUnary sealRowUnary windowsSealDiagonal
  have realUnary : UnaryHistory realRead :=
    unary_cont_closed diagonalUnary transportsUnary diagonalTransportsReal
  have completionUnary : UnaryHistory completionRead :=
    unary_cont_closed realUnary routesUnary realRoutesCompletion
  exact
    ⟨windowsUnary, toleranceUnary, tailUnary, sealRowUnary, transportsUnary, routesUnary,
      provenanceUnary, diagonalUnary, realUnary, completionUnary, indexWindowsModulus,
      modulusToleranceTail, windowsSealDiagonal, diagonalTransportsReal, realRoutesCompletion,
      namePkg, completionPkg⟩

end BEDC.Derived.UniformCauchyCriterionUp
