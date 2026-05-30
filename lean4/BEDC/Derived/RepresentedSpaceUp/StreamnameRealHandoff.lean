import BEDC.Derived.RepresentedSpaceUp

namespace BEDC.Derived.RepresentedSpaceUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem RepresentedSpaceStreamnameRealHandoff [AskSetup] [PackageSetup]
    {name schedule relation target transport replay provenance localName regRead realSeal : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    BEDC.Derived.RepresentedSpaceUp name schedule relation target transport replay provenance
        localName bundle pkg →
      Cont target localName regRead →
        Cont regRead provenance realSeal →
          PkgSig bundle realSeal pkg →
            SemanticNameCert
                (fun row : BHist => hsame row realSeal ∧ UnaryHistory row)
                (fun row : BHist =>
                  hsame row schedule ∨ hsame row relation ∨ hsame row target ∨
                    hsame row regRead ∨ hsame row realSeal ∨ hsame row provenance)
                (fun row : BHist =>
                  UnaryHistory row ∧ Cont target localName regRead ∧
                    Cont regRead provenance realSeal ∧ PkgSig bundle provenance pkg ∧
                      PkgSig bundle realSeal pkg)
                hsame ∧
              UnaryHistory regRead ∧ UnaryHistory realSeal := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle PkgSig SemanticNameCert hsame UnaryHistory
  intro carrier targetLocalNameRead readProvenanceSeal realSealPkg
  obtain ⟨_nameUnary, _scheduleUnary, _relationUnary, targetUnary, _transportUnary,
    _replayUnary, provenanceUnary, localNameUnary, _nameScheduleReplay,
    _relationTargetTransport, _localNameTransport, provenancePkg⟩ := carrier
  have regReadUnary : UnaryHistory regRead :=
    unary_cont_closed targetUnary localNameUnary targetLocalNameRead
  have realSealUnary : UnaryHistory realSeal :=
    unary_cont_closed regReadUnary provenanceUnary readProvenanceSeal
  have sourceRealSeal :
      (fun row : BHist => hsame row realSeal ∧ UnaryHistory row) realSeal := by
    exact ⟨hsame_refl realSeal, realSealUnary⟩
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row realSeal ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row schedule ∨ hsame row relation ∨ hsame row target ∨
              hsame row regRead ∨ hsame row realSeal ∨ hsame row provenance)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont target localName regRead ∧
              Cont regRead provenance realSeal ∧ PkgSig bundle provenance pkg ∧
                PkgSig bundle realSeal pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro realSeal sourceRealSeal
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
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl source.left))))
    ledger_sound := by
      intro _row source
      exact
        ⟨source.right, targetLocalNameRead, readProvenanceSeal, provenancePkg,
          realSealPkg⟩
  }
  exact ⟨cert, regReadUnary, realSealUnary⟩

end BEDC.Derived.RepresentedSpaceUp
