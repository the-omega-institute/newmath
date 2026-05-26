import BEDC.Derived.KleeneTreeUp.TasteGate
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.KleeneTreeUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def KleeneTreeCarrier [AskSetup] [PackageSetup]
    (tree boolLedger listSpine stream obstruction transport traversal provenance localName :
      BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  UnaryHistory tree ∧ UnaryHistory boolLedger ∧ UnaryHistory listSpine ∧
    UnaryHistory stream ∧ UnaryHistory obstruction ∧ UnaryHistory transport ∧
      UnaryHistory traversal ∧ UnaryHistory provenance ∧ UnaryHistory localName ∧
        PkgSig bundle provenance pkg ∧ PkgSig bundle localName pkg

theorem KleeneTreeNameCert_obligations [AskSetup] [PackageSetup]
    {tree boolLedger listSpine stream obstruction transport traversal provenance localName
      request prefixRead nodeRead obstructionRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    KleeneTreeCarrier tree boolLedger listSpine stream obstruction transport traversal provenance
        localName bundle pkg →
      Cont stream listSpine prefixRead →
        Cont prefixRead boolLedger nodeRead →
          Cont nodeRead obstruction obstructionRead →
            PkgSig bundle obstructionRead pkg →
              SemanticNameCert
                  (fun row : BHist => hsame row obstructionRead ∧ UnaryHistory row)
                  (fun row : BHist =>
                    hsame row tree ∨ hsame row boolLedger ∨ hsame row listSpine ∨
                      hsame row stream ∨ hsame row obstruction ∨
                        hsame row obstructionRead)
                  (fun row : BHist =>
                    hsame row obstructionRead ∧ PkgSig bundle obstructionRead pkg)
                  hsame ∧
                UnaryHistory tree ∧ UnaryHistory stream ∧ UnaryHistory obstruction ∧
                  Cont stream listSpine prefixRead ∧
                    Cont prefixRead boolLedger nodeRead ∧
                      Cont nodeRead obstruction obstructionRead ∧
                        PkgSig bundle provenance pkg ∧
                          PkgSig bundle obstructionRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont SemanticNameCert hsame UnaryHistory
  intro carrier streamPrefix prefixNode nodeObstruction obstructionPkg
  obtain ⟨treeUnary, boolUnary, listUnary, streamUnary, obstructionUnary, _transportUnary,
    _traversalUnary, _provenanceUnary, _localNameUnary, provenancePkg, _localNamePkg⟩ :=
    carrier
  have prefixUnary : UnaryHistory prefixRead :=
    unary_cont_closed streamUnary listUnary streamPrefix
  have nodeUnary : UnaryHistory nodeRead :=
    unary_cont_closed prefixUnary boolUnary prefixNode
  have obstructionReadUnary : UnaryHistory obstructionRead :=
    unary_cont_closed nodeUnary obstructionUnary nodeObstruction
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row obstructionRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row tree ∨ hsame row boolLedger ∨ hsame row listSpine ∨
              hsame row stream ∨ hsame row obstruction ∨ hsame row obstructionRead)
          (fun row : BHist =>
            hsame row obstructionRead ∧ PkgSig bundle obstructionRead pkg)
          hsame := {
    core := {
      carrier_inhabited :=
        Exists.intro obstructionRead ⟨hsame_refl obstructionRead, obstructionReadUnary⟩
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
        intro _row _other sameRows source
        exact
          ⟨hsame_trans (hsame_symm sameRows) source.left,
            unary_transport source.right sameRows⟩
    }
    pattern_sound := by
      intro _row source
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr source.left))))
    ledger_sound := by
      intro _row source
      exact ⟨source.left, obstructionPkg⟩
  }
  exact
    ⟨cert, treeUnary, streamUnary, obstructionUnary, streamPrefix, prefixNode,
      nodeObstruction, provenancePkg, obstructionPkg⟩

theorem KleeneTree_streamname_path_boundary [AskSetup] [PackageSetup]
    {tree boolLedger listSpine stream obstruction transport traversal provenance localName
      prefixRead nodeRead obstructionRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    KleeneTreeCarrier tree boolLedger listSpine stream obstruction transport traversal provenance
        localName bundle pkg →
      Cont stream listSpine prefixRead →
        Cont prefixRead boolLedger nodeRead →
          Cont nodeRead obstruction obstructionRead →
            PkgSig bundle provenance pkg →
              UnaryHistory stream ∧ UnaryHistory prefixRead ∧ UnaryHistory nodeRead ∧
                UnaryHistory obstructionRead ∧ PkgSig bundle provenance pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont UnaryHistory
  intro carrier streamPrefix prefixNode nodeObstruction provenancePkg
  obtain ⟨_treeUnary, boolUnary, listUnary, streamUnary, obstructionUnary, _transportUnary,
    _traversalUnary, _provenanceUnary, _localNameUnary, _carrierProvenancePkg,
      _localNamePkg⟩ := carrier
  have prefixUnary : UnaryHistory prefixRead :=
    unary_cont_closed streamUnary listUnary streamPrefix
  have nodeUnary : UnaryHistory nodeRead :=
    unary_cont_closed prefixUnary boolUnary prefixNode
  have obstructionReadUnary : UnaryHistory obstructionRead :=
    unary_cont_closed nodeUnary obstructionUnary nodeObstruction
  exact ⟨streamUnary, prefixUnary, nodeUnary, obstructionReadUnary, provenancePkg⟩

theorem KleeneTree_fan_boundary [AskSetup] [PackageSetup]
    {tree boolLedger listSpine stream obstruction transport traversal provenance localName
      streamRead spineRead boolRead _treeRead obstructionRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    KleeneTreeCarrier tree boolLedger listSpine stream obstruction transport traversal provenance
        localName bundle pkg →
      Cont stream listSpine streamRead →
        Cont streamRead boolLedger spineRead →
          Cont spineRead tree boolRead →
            Cont boolRead obstruction obstructionRead →
              PkgSig bundle obstructionRead pkg →
                UnaryHistory stream ∧ UnaryHistory listSpine ∧ UnaryHistory boolLedger ∧
                  UnaryHistory tree ∧ UnaryHistory obstruction ∧ UnaryHistory obstructionRead ∧
                    Cont stream listSpine streamRead ∧ Cont streamRead boolLedger spineRead ∧
                      Cont spineRead tree boolRead ∧ Cont boolRead obstruction obstructionRead ∧
                        PkgSig bundle provenance pkg ∧ PkgSig bundle obstructionRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig UnaryHistory
  intro carrier streamSpine spineBool boolTree treeObstruction obstructionPkg
  obtain ⟨treeUnary, boolUnary, listUnary, streamUnary, obstructionUnary, _transportUnary,
    _traversalUnary, _provenanceUnary, _localNameUnary, provenancePkg, _localNamePkg⟩ :=
    carrier
  have streamReadUnary : UnaryHistory streamRead :=
    unary_cont_closed streamUnary listUnary streamSpine
  have spineReadUnary : UnaryHistory spineRead :=
    unary_cont_closed streamReadUnary boolUnary spineBool
  have boolReadUnary : UnaryHistory boolRead :=
    unary_cont_closed spineReadUnary treeUnary boolTree
  have obstructionReadUnary : UnaryHistory obstructionRead :=
    unary_cont_closed boolReadUnary obstructionUnary treeObstruction
  exact
    ⟨streamUnary, listUnary, boolUnary, treeUnary, obstructionUnary, obstructionReadUnary,
      streamSpine, spineBool, boolTree, treeObstruction, provenancePkg, obstructionPkg⟩

end BEDC.Derived.KleeneTreeUp
