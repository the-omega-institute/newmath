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

theorem GeneratorFixedPointPacket_transport_row [AskSetup] [PackageSetup]
    {generator list classifier witness output transport routes provenance name generator' list'
      classifier' witness' output' routes' : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    GeneratorFixedPointPacket generator list classifier witness output transport routes
        provenance name bundle pkg →
      hsame generator generator' →
        hsame list list' →
          hsame classifier classifier' →
            hsame witness witness' →
              hsame output output' →
                hsame routes routes' →
                  Cont generator' list' classifier' →
                    Cont witness' output' routes' →
                      UnaryHistory generator' ∧ UnaryHistory list' ∧
                        UnaryHistory classifier' ∧ UnaryHistory witness' ∧
                          UnaryHistory output' ∧ UnaryHistory routes' ∧
                            Cont generator' list' classifier' ∧
                              Cont witness' output' routes' ∧ PkgSig bundle name pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame UnaryHistory
  intro packet sameGenerator sameList sameClassifier sameWitness sameOutput sameRoutes
    generatorListClassifier witnessOutputRoutes
  obtain ⟨generatorUnary, listUnary, classifierUnary, witnessUnary, outputUnary,
    _transportUnary, routesUnary, _provenanceUnary, _nameUnary, _generatorListClassifier,
    _witnessOutputRoutes, namePkg⟩ := packet
  have generatorUnary' : UnaryHistory generator' :=
    unary_transport generatorUnary sameGenerator
  have listUnary' : UnaryHistory list' :=
    unary_transport listUnary sameList
  have classifierUnary' : UnaryHistory classifier' :=
    unary_transport classifierUnary sameClassifier
  have witnessUnary' : UnaryHistory witness' :=
    unary_transport witnessUnary sameWitness
  have outputUnary' : UnaryHistory output' :=
    unary_transport outputUnary sameOutput
  have routesUnary' : UnaryHistory routes' :=
    unary_transport routesUnary sameRoutes
  exact
    ⟨generatorUnary',
      listUnary',
      classifierUnary',
      witnessUnary',
      outputUnary',
      routesUnary',
      generatorListClassifier,
      witnessOutputRoutes,
      namePkg⟩

theorem GeneratorFixedPointPacket_witness_ledger_row [AskSetup] [PackageSetup]
    {generator list classifier witness output transport routes provenance name witnessRead :
      BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    GeneratorFixedPointPacket generator list classifier witness output transport routes
        provenance name bundle pkg →
      Cont witness output witnessRead →
        PkgSig bundle witnessRead pkg →
          UnaryHistory witness ∧ UnaryHistory output ∧ UnaryHistory witnessRead ∧
            Cont witness output routes ∧ Cont witness output witnessRead ∧
              PkgSig bundle name pkg ∧ PkgSig bundle witnessRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont UnaryHistory
  intro packet witnessOutputRead witnessReadPkg
  obtain ⟨_generatorUnary, _listUnary, _classifierUnary, witnessUnary, outputUnary,
    _transportUnary, _routesUnary, _provenanceUnary, _nameUnary, _generatorListClassifier,
    witnessOutputRoutes, namePkg⟩ := packet
  have witnessReadUnary : UnaryHistory witnessRead :=
    unary_cont_closed witnessUnary outputUnary witnessOutputRead
  exact
    ⟨witnessUnary, outputUnary, witnessReadUnary, witnessOutputRoutes, witnessOutputRead,
      namePkg, witnessReadPkg⟩

end BEDC.Derived.GeneratorFixedPointUp
