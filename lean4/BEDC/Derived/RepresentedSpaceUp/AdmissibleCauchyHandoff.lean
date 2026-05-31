import BEDC.Derived.RepresentedSpaceUp

namespace BEDC.Derived.RepresentedSpaceUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem RepresentedSpaceCarrier_admissible_cauchy_handoff [AskSetup] [PackageSetup]
    {name schedule relation target transport replay provenance localName cauchyRead realSeal
      admissibleRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    BEDC.Derived.RepresentedSpaceUp name schedule relation target transport replay provenance
        localName bundle pkg →
      Cont target localName cauchyRead →
        Cont cauchyRead provenance realSeal →
          Cont realSeal replay admissibleRead →
            PkgSig bundle admissibleRead pkg →
              SemanticNameCert
                  (fun row : BHist => hsame row admissibleRead ∧ UnaryHistory row)
                  (fun row : BHist =>
                    hsame row schedule ∨ hsame row relation ∨ hsame row target ∨
                      hsame row cauchyRead ∨ hsame row realSeal ∨
                        hsame row admissibleRead ∨ hsame row provenance)
                  (fun row : BHist =>
                    UnaryHistory row ∧ Cont target localName cauchyRead ∧
                      Cont cauchyRead provenance realSeal ∧
                        Cont realSeal replay admissibleRead ∧
                          PkgSig bundle provenance pkg ∧ PkgSig bundle admissibleRead pkg)
                  hsame ∧
                UnaryHistory cauchyRead ∧ UnaryHistory realSeal ∧
                  UnaryHistory admissibleRead ∧ PkgSig bundle provenance pkg := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle PkgSig SemanticNameCert hsame UnaryHistory
  intro carrier targetLocalCauchy cauchyProvenanceSeal sealReplayAdmissible
    admissiblePkg
  obtain ⟨_nameUnary, _scheduleUnary, _relationUnary, targetUnary, _transportUnary,
    replayUnary, provenanceUnary, localNameUnary, _nameScheduleReplay,
    _relationTargetTransport, _localNameTransport, provenancePkg⟩ := carrier
  have cauchyUnary : UnaryHistory cauchyRead :=
    unary_cont_closed targetUnary localNameUnary targetLocalCauchy
  have realSealUnary : UnaryHistory realSeal :=
    unary_cont_closed cauchyUnary provenanceUnary cauchyProvenanceSeal
  have admissibleUnary : UnaryHistory admissibleRead :=
    unary_cont_closed realSealUnary replayUnary sealReplayAdmissible
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row admissibleRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row schedule ∨ hsame row relation ∨ hsame row target ∨
              hsame row cauchyRead ∨ hsame row realSeal ∨ hsame row admissibleRead ∨
                hsame row provenance)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont target localName cauchyRead ∧
              Cont cauchyRead provenance realSeal ∧ Cont realSeal replay admissibleRead ∧
                PkgSig bundle provenance pkg ∧ PkgSig bundle admissibleRead pkg)
          hsame := {
    core := {
      carrier_inhabited :=
        Exists.intro admissibleRead ⟨hsame_refl admissibleRead, admissibleUnary⟩
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
                  (Or.inl source.left)))))
    ledger_sound := by
      intro _row source
      exact
        ⟨source.right, targetLocalCauchy, cauchyProvenanceSeal, sealReplayAdmissible,
          provenancePkg, admissiblePkg⟩
  }
  exact ⟨cert, cauchyUnary, realSealUnary, admissibleUnary, provenancePkg⟩

end BEDC.Derived.RepresentedSpaceUp
