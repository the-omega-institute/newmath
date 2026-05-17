import BEDC.Derived.UniformCauchyCriterionUp.DiagonalExitClassifier
import BEDC.Derived.UniformCauchyCriterionUp.DiagonalUniquenessExit

namespace BEDC.Derived.UniformCauchyCriterionUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem UniformCauchyCriterionPacket_diagonal_exit_nonescape [AskSetup] [PackageSetup]
    {index windows modulus tolerance tail sealRow transports routes provenance name diagonalRead
      tailRead realRead realRead' classifierRead completionRead phaseRead hostTail : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    UniformCauchyCriterionPacket index windows modulus tolerance tail sealRow transports routes
        provenance name bundle pkg ->
      Cont index windows diagonalRead ->
      Cont diagonalRead tail tailRead ->
      Cont tail sealRow realRead ->
      Cont tail sealRow realRead' ->
      Cont tailRead realRead classifierRead ->
      Cont classifierRead provenance completionRead ->
      Cont completionRead name phaseRead ->
      PkgSig bundle classifierRead pkg ->
      PkgSig bundle phaseRead pkg ->
      UnaryHistory classifierRead ∧ UnaryHistory completionRead ∧ UnaryHistory phaseRead ∧
        hsame realRead realRead' ∧ Cont tailRead realRead classifierRead ∧
          Cont classifierRead provenance completionRead ∧ PkgSig bundle name pkg ∧
            PkgSig bundle classifierRead pkg ∧ PkgSig bundle phaseRead pkg ∧
              (Cont classifierRead (BHist.e0 hostTail) tailRead -> False) ∧
                (Cont classifierRead (BHist.e1 hostTail) tailRead -> False) := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame UnaryHistory PkgSig
  intro packet indexWindowsDiagonal diagonalTailRead tailSealReal tailSealReal'
    tailReadRealClassifier classifierProvenanceCompletion completionNamePhase classifierPkg
    phasePkg
  have classifierData :=
    UniformCauchyCriterionPacket_diagonal_exit_classifier
      (index := index) (windows := windows) (modulus := modulus) (tolerance := tolerance)
      (tail := tail) (sealRow := sealRow) (transports := transports) (routes := routes)
      (provenance := provenance) (name := name) (diagonalRead := diagonalRead)
      (tailRead := tailRead) (realRead := realRead) (realRead' := realRead')
      (classifierRead := classifierRead) (bundle := bundle) (pkg := pkg)
      packet indexWindowsDiagonal diagonalTailRead tailSealReal tailSealReal'
      tailReadRealClassifier classifierPkg
  have exitData :=
    UniformCauchyCriterionPacket_diagonal_uniqueness_exit
      (index := index) (windows := windows) (modulus := modulus) (tolerance := tolerance)
      (tail := tail) (sealRow := sealRow) (transports := transports) (routes := routes)
      (provenance := provenance) (name := name) (diagonalRead := diagonalRead)
      (tailRead := tailRead) (realRead := realRead) (classifierRead := classifierRead)
      (completionRead := completionRead) (phaseRead := phaseRead) (hostTail := hostTail)
      (bundle := bundle) (pkg := pkg) packet indexWindowsDiagonal diagonalTailRead
      tailSealReal tailReadRealClassifier classifierProvenanceCompletion completionNamePhase
      phasePkg
  obtain ⟨_diagonalUnary, _tailReadUnary, _realUnary, classifierUnary, sameReal,
    _diagonalTail, classifierCont, namePkg, classifierPkg'⟩ := classifierData
  obtain ⟨_diagonalUnary', _tailReadUnary', _realUnary', _classifierUnary',
    completionUnary, phaseUnary, _sameModulus, _diagonalTail', _classifierCont',
    completionCont, _namePkg', phasePkg', exitE0, exitE1⟩ := exitData
  exact
    ⟨classifierUnary, completionUnary, phaseUnary, sameReal, classifierCont, completionCont,
      namePkg, classifierPkg', phasePkg', exitE0, exitE1⟩

end BEDC.Derived.UniformCauchyCriterionUp
