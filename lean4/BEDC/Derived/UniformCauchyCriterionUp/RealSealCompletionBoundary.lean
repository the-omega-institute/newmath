import BEDC.Derived.UniformCauchyCriterionUp

namespace BEDC.Derived.UniformCauchyCriterionUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem UniformCauchyCriterionPacket_real_seal_completion_boundary [AskSetup] [PackageSetup]
    {index windows modulus tolerance tail sealRow transports routes provenance name regseqRead
      realRead completionRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    UniformCauchyCriterionPacket index windows modulus tolerance tail sealRow transports routes
        provenance name bundle pkg ->
      Cont index tail regseqRead ->
        Cont tail sealRow realRead ->
          Cont realRead routes completionRead ->
            PkgSig bundle regseqRead pkg ->
              PkgSig bundle realRead pkg ->
                PkgSig bundle completionRead pkg ->
                  UnaryHistory regseqRead ∧ UnaryHistory realRead ∧
                    UnaryHistory completionRead ∧ Cont index windows modulus ∧
                      Cont modulus tolerance tail ∧ Cont tail sealRow realRead ∧
                        Cont realRead routes completionRead ∧ PkgSig bundle name pkg ∧
                          PkgSig bundle completionRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont UnaryHistory
  intro packet indexTailRegseq tailSealReal realRoutesCompletion _regseqPkg _realPkg
    completionPkg
  obtain ⟨indexUnary, _windowsUnary, _modulusUnary, _toleranceUnary, tailUnary,
    sealRowUnary, _transportsUnary, routesUnary, _provenanceUnary, _nameUnary,
    indexWindowsModulus, modulusToleranceTail, _tailSealRowTransports,
    _transportsRoutesProvenance, namePkg⟩ := packet
  have regseqUnary : UnaryHistory regseqRead :=
    unary_cont_closed indexUnary tailUnary indexTailRegseq
  have realUnary : UnaryHistory realRead :=
    unary_cont_closed tailUnary sealRowUnary tailSealReal
  have completionUnary : UnaryHistory completionRead :=
    unary_cont_closed realUnary routesUnary realRoutesCompletion
  exact
    ⟨regseqUnary, realUnary, completionUnary, indexWindowsModulus, modulusToleranceTail,
      tailSealReal, realRoutesCompletion, namePkg, completionPkg⟩

end BEDC.Derived.UniformCauchyCriterionUp
