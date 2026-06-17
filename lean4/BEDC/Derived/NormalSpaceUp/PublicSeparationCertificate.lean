import BEDC.Derived.NormalSpaceUp.TasteGate

namespace BEDC.Derived.NormalSpaceUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem NormalSpacePacket_public_separation_certificate [AskSetup] [PackageSetup]
    {topology closedLeft closedRight disjoint openLeft openRight transport replay provenance
      localName exported publicRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    NormalSpacePacket topology closedLeft closedRight disjoint openLeft openRight transport
        replay provenance localName exported bundle pkg ->
      Cont disjoint transport publicRead ->
        PkgSig bundle exported pkg ->
          PkgSig bundle publicRead pkg ->
            SemanticNameCert
                (fun row : BHist => hsame row publicRead ∧ UnaryHistory row)
                (fun row : BHist =>
                  hsame row topology ∨ hsame row closedLeft ∨ hsame row closedRight ∨
                    hsame row disjoint ∨ hsame row openLeft ∨ hsame row openRight ∨
                      hsame row transport ∨ hsame row exported ∨ hsame row publicRead)
                (fun row : BHist =>
                  UnaryHistory row ∧ Cont closedLeft closedRight disjoint ∧
                    Cont openLeft openRight transport ∧ Cont disjoint transport publicRead ∧
                      PkgSig bundle exported pkg ∧ PkgSig bundle publicRead pkg)
                hsame ∧
              UnaryHistory publicRead ∧ Cont provenance localName exported := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame SemanticNameCert UnaryHistory
  intro packet publicRoute exportedPkg publicPkg
  obtain ⟨_topologyUnary, _closedLeftUnary, _closedRightUnary, disjointUnary,
    _openLeftUnary, _openRightUnary, transportUnary, _replayUnary, _provenanceUnary,
    _localNameUnary, _exportedUnary, closedDisjoint, openTransport, _transportProvenance,
    provenanceExported, _localNamePkg⟩ := packet
  have publicUnary : UnaryHistory publicRead :=
    unary_cont_closed disjointUnary transportUnary publicRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row publicRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row topology ∨ hsame row closedLeft ∨ hsame row closedRight ∨
              hsame row disjoint ∨ hsame row openLeft ∨ hsame row openRight ∨
                hsame row transport ∨ hsame row exported ∨ hsame row publicRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont closedLeft closedRight disjoint ∧
              Cont openLeft openRight transport ∧ Cont disjoint transport publicRead ∧
                PkgSig bundle exported pkg ∧ PkgSig bundle publicRead pkg)
          hsame := {
    core := {
      carrier_inhabited :=
        Exists.intro publicRead ⟨hsame_refl publicRead, publicUnary⟩
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
      exact
        Or.inr
          (Or.inr
            (Or.inr
              (Or.inr
                (Or.inr
                  (Or.inr
                    (Or.inr
                      (Or.inr source.left)))))))
    ledger_sound := by
      intro _row source
      exact
        ⟨source.right, closedDisjoint, openTransport, publicRoute, exportedPkg,
          publicPkg⟩
  }
  exact ⟨cert, publicUnary, provenanceExported⟩

end BEDC.Derived.NormalSpaceUp
