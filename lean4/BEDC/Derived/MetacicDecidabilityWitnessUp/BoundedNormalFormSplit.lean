import BEDC.Derived.MetacicDecidabilityWitnessUp.TasteGate
import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.MetacicDecidabilityWitnessUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem MetacicDecidabilityWitnessBoundedNormalFormSplit [AskSetup] [PackageSetup]
    {typing sameTerm bounded finished refusal transport provenance localName boundedFinished
      normalRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    UnaryHistory typing →
      UnaryHistory sameTerm →
        UnaryHistory bounded →
          UnaryHistory finished →
            UnaryHistory refusal →
              UnaryHistory transport →
                Cont typing sameTerm boundedFinished →
                  Cont bounded finished normalRead →
                    Cont normalRead refusal transport →
                      PkgSig bundle provenance pkg →
                        PkgSig bundle localName pkg →
                          SemanticNameCert
                              (fun row : BHist =>
                                (hsame row boundedFinished ∨ hsame row normalRead ∨
                                  hsame row transport) ∧ UnaryHistory row)
                              (fun row : BHist =>
                                hsame row typing ∨ hsame row sameTerm ∨
                                  hsame row bounded ∨ hsame row finished ∨
                                    hsame row refusal ∨ hsame row boundedFinished ∨
                                      hsame row normalRead ∨ hsame row transport)
                              (fun row : BHist =>
                                UnaryHistory row ∧ Cont typing sameTerm boundedFinished ∧
                                  Cont bounded finished normalRead ∧
                                    Cont normalRead refusal transport ∧
                                      PkgSig bundle provenance pkg ∧
                                        PkgSig bundle localName pkg)
                              hsame ∧
                            UnaryHistory boundedFinished ∧ UnaryHistory normalRead ∧
                              UnaryHistory transport := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame SemanticNameCert UnaryHistory
  intro typingUnary sameTermUnary boundedUnary finishedUnary refusalUnary transportUnary
    typingSameTerm boundedFinishedNormal normalRefusal provenancePkg localNamePkg
  have boundedFinishedUnary : UnaryHistory boundedFinished :=
    unary_cont_closed typingUnary sameTermUnary typingSameTerm
  have normalReadUnary : UnaryHistory normalRead :=
    unary_cont_closed boundedUnary finishedUnary boundedFinishedNormal
  have sourceNormal :
      (fun row : BHist =>
        (hsame row boundedFinished ∨ hsame row normalRead ∨ hsame row transport) ∧
          UnaryHistory row) normalRead := by
    exact ⟨Or.inr (Or.inl (hsame_refl normalRead)), normalReadUnary⟩
  have cert :
      SemanticNameCert
          (fun row : BHist =>
            (hsame row boundedFinished ∨ hsame row normalRead ∨ hsame row transport) ∧
              UnaryHistory row)
          (fun row : BHist =>
            hsame row typing ∨ hsame row sameTerm ∨ hsame row bounded ∨
              hsame row finished ∨ hsame row refusal ∨ hsame row boundedFinished ∨
                hsame row normalRead ∨ hsame row transport)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont typing sameTerm boundedFinished ∧
              Cont bounded finished normalRead ∧ Cont normalRead refusal transport ∧
                PkgSig bundle provenance pkg ∧ PkgSig bundle localName pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro normalRead sourceNormal
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
        cases source.left with
        | inl sameBoundedFinished =>
            exact
              ⟨Or.inl (hsame_trans (hsame_symm sameRows) sameBoundedFinished),
                unary_transport source.right sameRows⟩
        | inr rest =>
            cases rest with
            | inl sameNormal =>
                exact
                  ⟨Or.inr (Or.inl (hsame_trans (hsame_symm sameRows) sameNormal)),
                    unary_transport source.right sameRows⟩
            | inr sameTransport =>
                exact
                  ⟨Or.inr (Or.inr (hsame_trans (hsame_symm sameRows) sameTransport)),
                    unary_transport source.right sameRows⟩
    }
    pattern_sound := by
      intro _row source
      cases source.left with
      | inl sameBoundedFinished =>
          exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl sameBoundedFinished)))))
      | inr rest =>
          cases rest with
          | inl sameNormal =>
              exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl sameNormal))))))
          | inr sameTransport =>
              exact
                Or.inr
                  (Or.inr
                    (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr sameTransport))))))
    ledger_sound := by
      intro _row source
      exact
        ⟨source.right, typingSameTerm, boundedFinishedNormal, normalRefusal,
          provenancePkg, localNamePkg⟩
  }
  exact ⟨cert, boundedFinishedUnary, normalReadUnary, transportUnary⟩

theorem MetacicDecidabilityWitness_bounded_normal_form_split [AskSetup] [PackageSetup]
    {typing sameTerm bounded finished refusal transport route provenance name checkerRead
      conversionRead normalRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    UnaryHistory typing →
      UnaryHistory sameTerm →
        UnaryHistory bounded →
          UnaryHistory finished →
            Cont typing sameTerm checkerRead →
              Cont bounded finished conversionRead →
                Cont checkerRead conversionRead normalRead →
                  PkgSig bundle normalRead pkg →
                    (∃ w : MetacicDecidabilityWitnessUp,
                        w =
                          MetacicDecidabilityWitnessUp.mk typing sameTerm bounded finished
                            refusal transport route provenance name) ∧
                      SemanticNameCert
                          (fun row : BHist => hsame row normalRead ∧ UnaryHistory row)
                          (fun row : BHist =>
                            hsame row typing ∨ hsame row sameTerm ∨ hsame row bounded ∨
                              hsame row finished ∨ hsame row normalRead)
                          (fun row : BHist =>
                            UnaryHistory row ∧ Cont typing sameTerm checkerRead ∧
                              Cont bounded finished conversionRead ∧
                                Cont checkerRead conversionRead normalRead ∧
                                  PkgSig bundle normalRead pkg)
                          hsame ∧
                        UnaryHistory checkerRead ∧ UnaryHistory conversionRead ∧
                          UnaryHistory normalRead := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle PkgSig SemanticNameCert UnaryHistory
  intro typingUnary sameTermUnary boundedUnary finishedUnary checkerRoute conversionRoute
    normalRoute normalPkg
  have checkerUnary : UnaryHistory checkerRead :=
    unary_cont_closed typingUnary sameTermUnary checkerRoute
  have conversionUnary : UnaryHistory conversionRead :=
    unary_cont_closed boundedUnary finishedUnary conversionRoute
  have normalUnary : UnaryHistory normalRead :=
    unary_cont_closed checkerUnary conversionUnary normalRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row normalRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row typing ∨ hsame row sameTerm ∨ hsame row bounded ∨
              hsame row finished ∨ hsame row normalRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont typing sameTerm checkerRead ∧
              Cont bounded finished conversionRead ∧ Cont checkerRead conversionRead normalRead ∧
                PkgSig bundle normalRead pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro normalRead ⟨hsame_refl normalRead, normalUnary⟩
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
      exact Or.inr (Or.inr (Or.inr (Or.inr source.left)))
    ledger_sound := by
      intro _row source
      exact ⟨source.right, checkerRoute, conversionRoute, normalRoute, normalPkg⟩
  }
  exact
    ⟨⟨MetacicDecidabilityWitnessUp.mk typing sameTerm bounded finished refusal transport route
          provenance name, rfl⟩,
      cert, checkerUnary, conversionUnary, normalUnary⟩

end BEDC.Derived.MetacicDecidabilityWitnessUp
