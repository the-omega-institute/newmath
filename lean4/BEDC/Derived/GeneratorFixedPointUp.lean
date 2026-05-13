import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.GeneratorFixedPointUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def GeneratorFixedPointPacket [AskSetup] [PackageSetup]
    (generator list classifier witness output transport routes provenance name : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  UnaryHistory generator ∧ UnaryHistory list ∧ UnaryHistory classifier ∧
    UnaryHistory witness ∧ UnaryHistory output ∧ UnaryHistory transport ∧
      UnaryHistory routes ∧ UnaryHistory provenance ∧ UnaryHistory name ∧
        Cont generator list classifier ∧ Cont witness output routes ∧
          PkgSig bundle name pkg

theorem GeneratorFixedPointPacket_source_admission_row [AskSetup] [PackageSetup]
    {generator list classifier witness output transport routes provenance name admitted : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg}
    (packet :
      GeneratorFixedPointPacket generator list classifier witness output transport routes
        provenance name bundle pkg)
    (generatorListAdmitted : Cont generator list admitted)
    (admittedPkg : PkgSig bundle admitted pkg) :
    UnaryHistory generator ∧ UnaryHistory list ∧ UnaryHistory admitted ∧
      Cont generator list admitted ∧ Cont witness output routes ∧
        PkgSig bundle name pkg ∧ PkgSig bundle admitted pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont UnaryHistory
  obtain ⟨generatorUnary, listUnary, _classifierUnary, _witnessUnary, _outputUnary,
    _transportUnary, _routesUnary, _provenanceUnary, _nameUnary, _generatorClassifier,
    witnessOutputRoutes, namePkg⟩ := packet
  have admittedUnary : UnaryHistory admitted :=
    unary_cont_closed generatorUnary listUnary generatorListAdmitted
  exact
    ⟨generatorUnary,
      listUnary,
      admittedUnary,
      generatorListAdmitted,
      witnessOutputRoutes,
      namePkg,
      admittedPkg⟩

end BEDC.Derived.GeneratorFixedPointUp
