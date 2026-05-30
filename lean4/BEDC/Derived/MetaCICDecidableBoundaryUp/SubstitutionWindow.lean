import BEDC.Derived.MetaCICDecidableBoundaryUp.TasteGate
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package.Core
import BEDC.FKernel.Unary.History

namespace BEDC.Derived.MetaCICDecidableBoundaryUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem MetaCICDecidableBoundarySubstitutionWindow [AskSetup] [PackageSetup]
    {checker structural boundedNormal finished transport provenance localName boundedRead
      substitutionRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    UnaryHistory checker →
      UnaryHistory structural →
        UnaryHistory finished →
          UnaryHistory transport →
            Cont checker structural boundedNormal →
              Cont boundedNormal finished boundedRead →
                Cont boundedRead transport substitutionRead →
                  PkgSig bundle provenance pkg →
                    PkgSig bundle localName pkg →
                      SemanticNameCert
                          (fun row : BHist => hsame row substitutionRead ∧ UnaryHistory row)
                          (fun row : BHist =>
                            hsame row checker ∨ hsame row structural ∨
                              hsame row boundedNormal ∨ hsame row finished ∨
                                hsame row boundedRead ∨ hsame row substitutionRead ∨
                                  hsame row localName)
                          (fun row : BHist =>
                            UnaryHistory row ∧ Cont checker structural boundedNormal ∧
                              Cont boundedNormal finished boundedRead ∧
                                Cont boundedRead transport substitutionRead ∧
                                  PkgSig bundle localName pkg)
                          hsame ∧
                        UnaryHistory boundedNormal ∧ UnaryHistory boundedRead ∧
                          UnaryHistory substitutionRead := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame SemanticNameCert
  intro checkerUnary structuralUnary finishedUnary transportUnary
  intro checkerStructuralBounded boundedFinishedRead boundedTransportSubstitution
  intro _provenancePkg localPkg
  have boundedNormalUnary : UnaryHistory boundedNormal :=
    unary_cont_closed checkerUnary structuralUnary checkerStructuralBounded
  have boundedReadUnary : UnaryHistory boundedRead :=
    unary_cont_closed boundedNormalUnary finishedUnary boundedFinishedRead
  have substitutionReadUnary : UnaryHistory substitutionRead :=
    unary_cont_closed boundedReadUnary transportUnary boundedTransportSubstitution
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row substitutionRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row checker ∨ hsame row structural ∨ hsame row boundedNormal ∨
              hsame row finished ∨ hsame row boundedRead ∨ hsame row substitutionRead ∨
                hsame row localName)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont checker structural boundedNormal ∧
              Cont boundedNormal finished boundedRead ∧
                Cont boundedRead transport substitutionRead ∧ PkgSig bundle localName pkg)
          hsame := {
    core := {
      carrier_inhabited :=
        Exists.intro substitutionRead ⟨hsame_refl substitutionRead, substitutionReadUnary⟩
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
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl source.left)))))
    ledger_sound := by
      intro _row source
      exact
        ⟨source.right, checkerStructuralBounded, boundedFinishedRead,
          boundedTransportSubstitution, localPkg⟩
  }
  exact ⟨cert, boundedNormalUnary, boundedReadUnary, substitutionReadUnary⟩

end BEDC.Derived.MetaCICDecidableBoundaryUp
