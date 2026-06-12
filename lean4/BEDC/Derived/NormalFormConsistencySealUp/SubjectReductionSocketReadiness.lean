import BEDC.Derived.NormalFormConsistencySealUp
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package

namespace BEDC.Derived.NormalFormConsistencySealUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem NormalFormConsistencySealSubjectReductionSocketReadiness [AskSetup] [PackageSetup]
    {typing falseRow normality checked boundary transport replay provenance localName
      socketRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    UnaryHistory boundary →
      UnaryHistory transport →
        PkgSig bundle provenance pkg →
          PkgSig bundle localName pkg →
            Cont boundary transport socketRead →
              SemanticNameCert
                  (fun row : BHist => hsame row socketRead ∧ UnaryHistory row)
                  (fun row : BHist =>
                    hsame row boundary ∨ hsame row checked ∨ hsame row socketRead)
                  (fun row : BHist =>
                    UnaryHistory row ∧ PkgSig bundle provenance pkg ∧
                      PkgSig bundle localName pkg)
                  hsame ∧
                UnaryHistory socketRead := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame SemanticNameCert UnaryHistory
  intro boundaryUnary transportUnary provenancePkg localNamePkg boundaryTransportRead
  have socketReadUnary : UnaryHistory socketRead :=
    unary_cont_closed boundaryUnary transportUnary boundaryTransportRead
  have sourceSocket :
      (fun row : BHist => hsame row socketRead ∧ UnaryHistory row) socketRead := by
    exact ⟨hsame_refl socketRead, socketReadUnary⟩
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row socketRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row boundary ∨ hsame row checked ∨ hsame row socketRead)
          (fun row : BHist =>
            UnaryHistory row ∧ PkgSig bundle provenance pkg ∧ PkgSig bundle localName pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro socketRead sourceSocket
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
      exact Or.inr (Or.inr source.left)
    ledger_sound := by
      intro _row source
      exact ⟨source.right, provenancePkg, localNamePkg⟩
  }
  exact ⟨cert, socketReadUnary⟩

end BEDC.Derived.NormalFormConsistencySealUp
