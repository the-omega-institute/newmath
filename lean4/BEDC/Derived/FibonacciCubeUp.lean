import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.FibonacciCubeUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def FibonacciCubePacket [AskSetup] [PackageSetup]
    (length graph word support zeckendorf deps provenance certificate : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  UnaryHistory length ∧ UnaryHistory graph ∧ UnaryHistory zeckendorf ∧
    UnaryHistory deps ∧ UnaryHistory provenance ∧ Cont length graph word ∧
      Cont word graph support ∧ Cont support zeckendorf deps ∧
        Cont deps provenance certificate ∧ PkgSig bundle certificate pkg

theorem FibonacciCubePacket_word_path_support_correspondence [AskSetup] [PackageSetup]
    {length graph word support zeckendorf deps provenance certificate supportRead
      independent : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    FibonacciCubePacket length graph word support zeckendorf deps provenance certificate bundle pkg ->
      Cont word graph supportRead ->
        Cont supportRead graph independent ->
          UnaryHistory word ∧ UnaryHistory graph ∧ UnaryHistory supportRead ∧
            UnaryHistory independent ∧ Cont word graph supportRead ∧
              Cont supportRead graph independent ∧ PkgSig bundle certificate pkg := by
  intro packet wordGraphSupportRead supportReadGraphIndependent
  obtain ⟨lengthUnary, graphUnary, _zeckendorfUnary, _depsUnary, _provenanceUnary,
    lengthGraphWord, _wordGraphSupport, _supportZeckendorfDeps, _depsProvenanceCertificate,
    certificatePkg⟩ := packet
  have wordUnary : UnaryHistory word :=
    unary_cont_closed lengthUnary graphUnary lengthGraphWord
  have supportReadUnary : UnaryHistory supportRead :=
    unary_cont_closed wordUnary graphUnary wordGraphSupportRead
  have independentUnary : UnaryHistory independent :=
    unary_cont_closed supportReadUnary graphUnary supportReadGraphIndependent
  exact
    ⟨wordUnary, graphUnary, supportReadUnary, independentUnary, wordGraphSupportRead,
      supportReadGraphIndependent, certificatePkg⟩

end BEDC.Derived.FibonacciCubeUp
