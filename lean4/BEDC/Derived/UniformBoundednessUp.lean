import BEDC.Derived.UniformBoundednessUp.TasteGate
import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package

namespace BEDC.Derived.UniformBoundednessUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package

def UniformBoundednessPacket [AskSetup] [PackageSetup]
    (family pointwise baire norm regseq stream transport history replay provenance nameRow :
      BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  hsame nameRow history ∧
          Cont family pointwise baire ∧
            Cont baire norm regseq ∧
              Cont regseq stream history ∧
                Cont transport history replay ∧
                  Cont replay provenance nameRow ∧
                    PkgSig bundle provenance pkg ∧ PkgSig bundle history pkg

theorem UniformBoundednessPacket_namecert_obligations [AskSetup] [PackageSetup]
    {family pointwise baire norm regseq stream transport history replay provenance nameRow :
      BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    UniformBoundednessPacket family pointwise baire norm regseq stream transport history replay
        provenance nameRow bundle pkg →
      SemanticNameCert
          (fun row : BHist =>
            hsame row history ∧
              UniformBoundednessPacket family pointwise baire norm regseq stream transport
                history replay provenance nameRow bundle pkg)
          (fun row : BHist =>
            hsame row history ∧ Cont family pointwise baire ∧ Cont baire norm regseq ∧
              Cont regseq stream history)
          (fun row : BHist => hsame row history ∧ PkgSig bundle history pkg) hsame ∧
        PkgSig bundle history pkg := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle Pkg SemanticNameCert hsame PkgSig
  intro packet
  rcases packet with
    ⟨sameNameHistory, familyPointwiseBaire, baireNormRegseq, regseqStreamHistory,
      transportHistoryReplay, replayProvenanceNameRow, packageProvenance,
      packageHistory⟩
  have packetAtHistory :
      hsame history history ∧
        UniformBoundednessPacket family pointwise baire norm regseq stream transport history
          replay provenance nameRow bundle pkg := by
    exact
      ⟨hsame_refl history, sameNameHistory, familyPointwiseBaire, baireNormRegseq,
        regseqStreamHistory, transportHistoryReplay, replayProvenanceNameRow,
        packageProvenance, packageHistory⟩
  have cert :
      SemanticNameCert
          (fun row : BHist =>
            hsame row history ∧
              UniformBoundednessPacket family pointwise baire norm regseq stream transport
                history replay provenance nameRow bundle pkg)
          (fun row : BHist =>
            hsame row history ∧ Cont family pointwise baire ∧ Cont baire norm regseq ∧
              Cont regseq stream history)
          (fun row : BHist => hsame row history ∧ PkgSig bundle history pkg) hsame := by
    exact {
      core := {
        carrier_inhabited := Exists.intro history packetAtHistory
        equiv_refl := by
          intro row _source
          exact hsame_refl row
        equiv_symm := by
          intro _row _other sameRows
          exact hsame_symm sameRows
        equiv_trans := by
          intro _row _middle _other sameLeft sameRight
          exact hsame_trans sameLeft sameRight
        carrier_respects_equiv := by
          intro _row other sameRows source
          exact
            ⟨hsame_trans (hsame_symm sameRows) source.left,
              sameNameHistory, familyPointwiseBaire, baireNormRegseq, regseqStreamHistory,
              transportHistoryReplay, replayProvenanceNameRow, packageProvenance,
              packageHistory⟩
      }
      pattern_sound := by
        intro _row source
        exact
          ⟨source.left, familyPointwiseBaire, baireNormRegseq, regseqStreamHistory⟩
      ledger_sound := by
        intro _row source
        exact ⟨source.left, packageHistory⟩
    }
  exact ⟨cert, packageHistory⟩

theorem UniformBoundedness_carrier_admission [AskSetup] [PackageSetup]
    {family pointwise baire norm regseq stream transport history replay provenance nameRow :
      BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    UniformBoundednessPacket family pointwise baire norm regseq stream transport history replay
        provenance nameRow bundle pkg ->
      hsame nameRow history ∧ Cont family pointwise baire ∧ Cont baire norm regseq ∧
        Cont regseq stream history ∧ Cont transport history replay ∧
          Cont replay provenance nameRow ∧ PkgSig bundle provenance pkg ∧
            PkgSig bundle history pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig hsame
  intro packet
  exact packet

theorem UniformBoundednessFamilyCoherence [AskSetup] [PackageSetup]
    {family pointwise baire norm regseq stream transport history replay provenance nameRow
      operatorRead normRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    UniformBoundednessPacket family pointwise baire norm regseq stream transport history replay
        provenance nameRow bundle pkg ->
      Cont family pointwise operatorRead ->
        Cont operatorRead norm normRead ->
          PkgSig bundle normRead pkg ->
            SemanticNameCert
                (fun row : BHist => hsame row normRead)
                (fun row : BHist =>
                  hsame row family ∨ hsame row pointwise ∨ hsame row operatorRead ∨
                    hsame row normRead)
                (fun row : BHist =>
                  hsame row normRead ∧ Cont family pointwise operatorRead ∧
                    Cont operatorRead norm normRead ∧ PkgSig bundle normRead pkg)
                hsame ∧
              PkgSig bundle history pkg := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle Pkg SemanticNameCert hsame PkgSig
  intro packet familyPointwiseOperator operatorNormRead normReadPkg
  rcases packet with
    ⟨sameNameHistory, familyPointwiseBaire, baireNormRegseq, regseqStreamHistory,
      transportHistoryReplay, replayProvenanceNameRow, packageProvenance,
      packageHistory⟩
  have sourceNorm :
      (fun row : BHist => hsame row normRead) normRead := by
    exact hsame_refl normRead
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row normRead)
          (fun row : BHist =>
            hsame row family ∨ hsame row pointwise ∨ hsame row operatorRead ∨
              hsame row normRead)
          (fun row : BHist =>
            hsame row normRead ∧ Cont family pointwise operatorRead ∧
              Cont operatorRead norm normRead ∧ PkgSig bundle normRead pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro normRead sourceNorm
      equiv_refl := by
        intro row _source
        exact hsame_refl row
      equiv_symm := by
        intro _row _other sameRows
        exact hsame_symm sameRows
      equiv_trans := by
        intro _row _middle _other sameLeft sameRight
        exact hsame_trans sameLeft sameRight
      carrier_respects_equiv := by
        intro _row _other sameRows sourceRow
        exact hsame_trans (hsame_symm sameRows) sourceRow
    }
    pattern_sound := by
      intro _row sourceRow
      exact Or.inr (Or.inr (Or.inr sourceRow))
    ledger_sound := by
      intro _row sourceRow
      exact ⟨sourceRow, familyPointwiseOperator, operatorNormRead, normReadPkg⟩
  }
  exact ⟨cert, packageHistory⟩

end BEDC.Derived.UniformBoundednessUp
