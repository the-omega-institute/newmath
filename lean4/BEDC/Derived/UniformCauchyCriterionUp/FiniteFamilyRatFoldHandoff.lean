import BEDC.Derived.UniformCauchyCriterionUp

namespace BEDC.Derived.UniformCauchyCriterionUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem UniformCauchyCriterionPacket_finite_family_rat_fold_handoff [AskSetup] [PackageSetup]
    {index windows modulus tolerance tail sealRow transports routes provenance name ratLeft
      ratRight ratFold sealFold : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    UniformCauchyCriterionPacket index windows modulus tolerance tail sealRow transports routes
        provenance name bundle pkg →
      Cont windows modulus ratLeft →
        Cont tolerance tail ratRight →
          Cont ratLeft ratRight ratFold →
            Cont ratFold sealRow sealFold →
              PkgSig bundle sealFold pkg →
                UnaryHistory ratLeft ∧ UnaryHistory ratRight ∧ UnaryHistory ratFold ∧
                  UnaryHistory sealFold ∧ Cont windows modulus ratLeft ∧
                    Cont tolerance tail ratRight ∧ Cont ratLeft ratRight ratFold ∧
                      Cont ratFold sealRow sealFold ∧ PkgSig bundle name pkg ∧
                        PkgSig bundle sealFold pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont UnaryHistory
  intro packet windowsModulusRatLeft toleranceTailRatRight ratLeftRightFold foldSealFold
    sealFoldPkg
  obtain ⟨_indexUnary, windowsUnary, modulusUnary, toleranceUnary, tailUnary, sealRowUnary,
    _transportsUnary, _routesUnary, _provenanceUnary, _nameUnary, _indexWindowsModulus,
    _modulusToleranceTail, _tailSealRowTransports, _transportsRoutesProvenance, namePkg⟩ :=
    packet
  have ratLeftUnary : UnaryHistory ratLeft :=
    unary_cont_closed windowsUnary modulusUnary windowsModulusRatLeft
  have ratRightUnary : UnaryHistory ratRight :=
    unary_cont_closed toleranceUnary tailUnary toleranceTailRatRight
  have ratFoldUnary : UnaryHistory ratFold :=
    unary_cont_closed ratLeftUnary ratRightUnary ratLeftRightFold
  have sealFoldUnary : UnaryHistory sealFold :=
    unary_cont_closed ratFoldUnary sealRowUnary foldSealFold
  exact
    ⟨ratLeftUnary, ratRightUnary, ratFoldUnary, sealFoldUnary, windowsModulusRatLeft,
      toleranceTailRatRight, ratLeftRightFold, foldSealFold, namePkg, sealFoldPkg⟩

end BEDC.Derived.UniformCauchyCriterionUp
