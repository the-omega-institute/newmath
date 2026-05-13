import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.AnalyticContinuationSocketUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

inductive AnalyticContinuationSocketUp : Type where
  | mk
      (source leftOverlap witness operation output branch transport continuation provenance name :
        BHist) :
      AnalyticContinuationSocketUp

def AnalyticContinuationSocketCarrier [AskSetup] [PackageSetup]
    (source leftOverlap witness operation output branch transport continuation provenance name :
      BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  UnaryHistory source ∧ UnaryHistory leftOverlap ∧ UnaryHistory witness ∧
    UnaryHistory operation ∧ UnaryHistory output ∧ UnaryHistory branch ∧
      UnaryHistory transport ∧ UnaryHistory continuation ∧ UnaryHistory provenance ∧
        UnaryHistory name ∧ Cont source leftOverlap witness ∧ Cont witness operation output ∧
          Cont branch transport continuation ∧ Cont continuation name provenance ∧
            PkgSig bundle provenance pkg

theorem AnalyticContinuationSocketCarrier_namecert_obligations [AskSetup] [PackageSetup]
    {source leftOverlap witness operation output branch transport continuation provenance name
      consumer : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    AnalyticContinuationSocketCarrier source leftOverlap witness operation output branch
        transport continuation provenance name bundle pkg →
      Cont output branch consumer →
        PkgSig bundle consumer pkg →
          UnaryHistory source ∧ UnaryHistory leftOverlap ∧ UnaryHistory witness ∧
            UnaryHistory operation ∧ UnaryHistory output ∧ UnaryHistory branch ∧
              UnaryHistory transport ∧ UnaryHistory continuation ∧ UnaryHistory provenance ∧
                UnaryHistory name ∧ UnaryHistory consumer ∧ Cont source leftOverlap witness ∧
                  Cont witness operation output ∧ Cont branch transport continuation ∧
                    Cont continuation name provenance ∧ Cont output branch consumer ∧
                      PkgSig bundle provenance pkg ∧ PkgSig bundle consumer pkg ∧
                        SemanticNameCert
                          (fun row : BHist => hsame row provenance ∧ UnaryHistory row)
                          (fun row : BHist => hsame row provenance)
                          (fun row : BHist => hsame row provenance ∧
                            PkgSig bundle provenance pkg)
                          hsame := by
  -- BEDC touchpoint anchor: BHist Cont hsame UnaryHistory Pkg
  intro carrier consumerRow consumerPkg
  have sourceUnary : UnaryHistory source :=
    carrier.left
  have leftOverlapUnary : UnaryHistory leftOverlap :=
    carrier.right.left
  have witnessUnary : UnaryHistory witness :=
    carrier.right.right.left
  have operationUnary : UnaryHistory operation :=
    carrier.right.right.right.left
  have outputUnary : UnaryHistory output :=
    carrier.right.right.right.right.left
  have branchUnary : UnaryHistory branch :=
    carrier.right.right.right.right.right.left
  have transportUnary : UnaryHistory transport :=
    carrier.right.right.right.right.right.right.left
  have continuationUnary : UnaryHistory continuation :=
    carrier.right.right.right.right.right.right.right.left
  have provenanceUnary : UnaryHistory provenance :=
    carrier.right.right.right.right.right.right.right.right.left
  have nameUnary : UnaryHistory name :=
    carrier.right.right.right.right.right.right.right.right.right.left
  have sourceOverlapWitness : Cont source leftOverlap witness :=
    carrier.right.right.right.right.right.right.right.right.right.right.left
  have witnessOperationOutput : Cont witness operation output :=
    carrier.right.right.right.right.right.right.right.right.right.right.right.left
  have branchTransportContinuation : Cont branch transport continuation :=
    carrier.right.right.right.right.right.right.right.right.right.right.right.right.left
  have continuationNameProvenance : Cont continuation name provenance :=
    carrier.right.right.right.right.right.right.right.right.right.right.right.right.right.left
  have provenancePkg : PkgSig bundle provenance pkg :=
    carrier.right.right.right.right.right.right.right.right.right.right.right.right.right.right
  have consumerUnary : UnaryHistory consumer :=
    unary_cont_closed outputUnary branchUnary consumerRow
  have cert :
      SemanticNameCert
        (fun row : BHist => hsame row provenance ∧ UnaryHistory row)
        (fun row : BHist => hsame row provenance)
        (fun row : BHist => hsame row provenance ∧ PkgSig bundle provenance pkg)
        hsame := {
    core := {
      carrier_inhabited := Exists.intro provenance
        (And.intro (hsame_refl provenance) provenanceUnary)
      equiv_refl := by
        intro row _source
        exact hsame_refl row
      equiv_symm := by
        intro row row' same
        exact hsame_symm same
      equiv_trans := by
        intro row row' row'' same same'
        exact hsame_trans same same'
      carrier_respects_equiv := by
        intro row row' same sourceRow
        exact And.intro (hsame_trans (hsame_symm same) sourceRow.left)
          (unary_transport sourceRow.right same)
    }
    pattern_sound := by
      intro _row sourceRow
      exact sourceRow.left
    ledger_sound := by
      intro _row sourceRow
      exact And.intro sourceRow.left provenancePkg
  }
  exact
    And.intro sourceUnary
      (And.intro leftOverlapUnary
        (And.intro witnessUnary
          (And.intro operationUnary
            (And.intro outputUnary
              (And.intro branchUnary
                (And.intro transportUnary
                  (And.intro continuationUnary
                    (And.intro provenanceUnary
                      (And.intro nameUnary
                        (And.intro consumerUnary
                          (And.intro sourceOverlapWitness
                            (And.intro witnessOperationOutput
                              (And.intro branchTransportContinuation
                                (And.intro continuationNameProvenance
                                  (And.intro consumerRow
                                    (And.intro provenancePkg
                                      (And.intro consumerPkg cert)))))))))))))))))

def AnalyticContinuationSocketPacket [AskSetup] [PackageSetup]
    (source leftOverlap witness operation output branch transport continuation provenance
      name : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  UnaryHistory source ∧ UnaryHistory leftOverlap ∧ UnaryHistory witness ∧
    UnaryHistory operation ∧ UnaryHistory output ∧ UnaryHistory branch ∧
      UnaryHistory provenance ∧ Cont source leftOverlap transport ∧
        Cont witness operation continuation ∧ PkgSig bundle name pkg

theorem AnalyticContinuationSocketPacket_overlap_transport [AskSetup] [PackageSetup]
    {source leftOverlap witness operation output branch transport continuation provenance
      name : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    AnalyticContinuationSocketPacket source leftOverlap witness operation output branch
        transport continuation provenance name bundle pkg →
      UnaryHistory source ∧ UnaryHistory leftOverlap ∧ UnaryHistory witness ∧
        Cont source leftOverlap transport ∧ Cont witness operation continuation ∧
          PkgSig bundle name pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont
  intro packet
  obtain ⟨sourceUnary, leftOverlapUnary, witnessUnary, _operationUnary, _outputUnary,
    _branchUnary, _provenanceUnary, overlapRoute, continuationRoute, namePkg⟩ := packet
  exact
    ⟨sourceUnary, leftOverlapUnary, witnessUnary, overlapRoute, continuationRoute, namePkg⟩

end BEDC.Derived.AnalyticContinuationSocketUp
